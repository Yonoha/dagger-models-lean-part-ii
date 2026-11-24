import DaggerModelsPartII.JTJointSubcomplexRelativeLift
import DaggerModelsPartII.OrderedSimplexEndpointFiber
import DaggerModelsPartII.ReversalDiscreteFreeColimits
import DaggerModelsPartII.JTNativeRowCoefficientOperators
import DaggerModelsPartII.JTTriangleBoundaryLabel

/-! Relative two-simplex fillers for unbased row-one seam edges. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open MonoidalCategory CartesianMonoidalCategory
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTRelativeSeamTriangle

open JTProjectiveOrderedFiberComparison (row vertexPoint)
open ReversalDiscreteFreeColimits (discreteFree)
open JTEndpointNormalizationLifts (identityFamily)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev boundary := (SSet.boundary 2).toSSet

/-- Mapping spaces on the literal two-simplex and its full boundary. -/
abbrev fullMapping (W : Source) :=
  diagramMappingSpace (discreteFree.obj (Δ[2] : SSet.{0})) W
abbrev boundaryMapping (W : Source) :=
  diagramMappingSpace (discreteFree.obj boundary) W

/-- The actual full-boundary restriction in the original reversal diagram. -/
def boundaryPrecomp (W : Source) : fullMapping W ⟶ boundaryMapping W :=
  diagramMappingPrecomp (discreteFree.map (SSet.boundary 2).ι) W

/-- Injective fibrancy gives the full two-simplex boundary restriction fibration. -/
theorem boundaryPrecomp_fibration (W : Source)
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    Fibration (boundaryPrecomp W) := by
  letI : ModelCategory Source :=
    InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
  letI : IsFibrant W := hW
  letI : Mono (discreteFree.map (SSet.boundary 2).ι) :=
    ReversalDiscreteFreeColimits.map_mono (SSet.boundary 2).ι
  exact InjectiveKanDiagram.diagramMappingPrecomp_isFibration
    ReverseSimplexᵒᵖ (discreteFree.map (SSet.boundary 2).ι) W

/-- The literal free two-simplex mapping space is the original row-two space. -/
def fullRowIso (W : Source) : fullMapping W ≅ row W ⦋2⦌ :=
  OrderedSimplexEndpointFiber.freeSimplexRowIso W 2

/-- The native horizontal degeneracy from one row vertex to a two-simplex. -/
def identityTriangle (W : Source) : row W ⦋0⦌ ⟶ row W ⦋2⦌ :=
  (JTRealizationDiagonal.ordinaryCurry.obj
    (JTReversalInput.ordinaryInput.obj W)).map
      (SimplexCategory.const ⦋2⦌ ⦋0⦌ 0).op

/-- The horizontal edge opposite vertex `j` of a row-two simplex. -/
def rowEdge (W : Source) (j : Fin 3) : row W ⦋2⦌ ⟶ row W ⦋1⦌ :=
  (JTRealizationDiagonal.ordinaryCurry.obj
    (JTReversalInput.ordinaryInput.obj W)).map (SimplexCategory.δ j).op

private theorem δ_zero_endpoint_one :
    SimplexCategory.δ (0 : Fin 2) =
      JTXiEndpointCollapseBoundary.ordinaryEndpoint (1 : Fin 2) := by
  apply SimplexCategory.Hom.ext
  decide

private theorem δ_one_endpoint_zero :
    SimplexCategory.δ (1 : Fin 2) =
      JTXiEndpointCollapseBoundary.ordinaryEndpoint (0 : Fin 2) := by
  apply SimplexCategory.Hom.ext
  decide

/-- Restriction of a free two-simplex along an ordinary face, before taking
the chosen row isomorphisms. -/
def fullEdgePrecomp (W : Source) (j : Fin 3) :
    fullMapping W ⟶ diagramMappingSpace (discreteFree.obj (Δ[1] : SSet.{0})) W :=
  diagramMappingPrecomp (discreteFree.map (std.map (SimplexCategory.δ j))) W

/-- The free-simplex to row identification carries face restriction to the
literal horizontal row face. -/
theorem fullEdgePrecomp_row (W : Source) (j : Fin 3) :
    (fullRowIso W).inv ≫ fullEdgePrecomp W j ≫
      (OrderedSimplexEndpointFiber.freeSimplexRowIso W 1).hom = rowEdge W j := by
  have h := JTNativeRowCoefficientOperators.freeSimplexRowIso_natural W
    (SimplexCategory.δ j)
  have hh := congrArg (fun g ↦ (fullRowIso W).inv ≫ g) h
  simpa only [fullRowIso, fullEdgePrecomp, rowEdge, Category.assoc,
    Iso.inv_hom_id_assoc] using hh

/-- All three edges of the stationary triangle are the identity edge. -/
theorem identityTriangle_edge (W : Source) (j : Fin 3) :
    identityTriangle W ≫ rowEdge W j = identityFamily W := by
  let C := JTRealizationDiagonal.ordinaryCurry.obj
    (JTReversalInput.ordinaryInput.obj W)
  change C.map (SimplexCategory.const ⦋2⦌ ⦋0⦌ 0).op ≫
    C.map (SimplexCategory.δ j).op =
      C.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op
  rw [← C.map_comp, ← op_comp]
  congr 1

/-- The prescribed stationary triangle on an arbitrary support. -/
def stationaryMapping (W : Source) {U : SSet.{0}}
    (z : (row W ⦋0⦌).obj (op ⦋0⦌)) : U ⟶ fullMapping W :=
  term U ≫ vertexPoint W z ≫ identityTriangle W ≫ (fullRowIso W).inv

theorem stationaryMapping_row (W : Source) {U : SSet.{0}}
    (z : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    stationaryMapping W z ≫ (fullRowIso W).hom =
      term U ≫ vertexPoint W z ≫ identityTriangle W := by
  simp only [stationaryMapping, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Each boundary edge of the prescribed triangle is the stationary identity
edge on the support. -/
theorem stationaryMapping_edge (W : Source) {U : SSet.{0}}
    (z : (row W ⦋0⦌).obj (op ⦋0⦌)) (j : Fin 3) :
    stationaryMapping W (U := U) z ≫ fullEdgePrecomp W j ≫
      (OrderedSimplexEndpointFiber.freeSimplexRowIso W 1).hom =
        JTJointSubcomplexRelativeLift.identityOnU W (U := U) z := by
  have h := congrArg (fun g ↦ (fullRowIso W).hom ≫ g)
    (fullEdgePrecomp_row W j)
  have hface : fullEdgePrecomp W j ≫
      (OrderedSimplexEndpointFiber.freeSimplexRowIso W 1).hom =
        (fullRowIso W).hom ≫ rowEdge W j := by
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h
  calc
    stationaryMapping W z ≫ fullEdgePrecomp W j ≫
        (OrderedSimplexEndpointFiber.freeSimplexRowIso W 1).hom =
      stationaryMapping W z ≫ (fullRowIso W).hom ≫ rowEdge W j := by
        simpa only [Category.assoc] using
          congrArg (fun g ↦ stationaryMapping W (U := U) z ≫ g) hface
    _ = JTJointSubcomplexRelativeLift.identityOnU W z := by
      have hh := congrArg (fun g ↦ g ≫ rowEdge W j)
        (stationaryMapping_row W (U := U) z)
      simpa only [Category.assoc, identityTriangle_edge,
        JTJointSubcomplexRelativeLift.identityOnU] using hh

/-- A compatible stationary boundary over a mono weak support has a full filler. -/
theorem exists_mapping_filler (W : Source) {U : SSet.{0}} {k : SimplexCategory}
    (i : U ⟶ std.obj k) [Mono i] [WeakEquivalence i]
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (stationary : U ⟶ fullMapping W)
    (b : std.obj k ⟶ boundaryMapping W)
    (h : stationary ≫ boundaryPrecomp W = i ≫ b) :
    ∃ t : std.obj k ⟶ fullMapping W,
      i ≫ t = stationary ∧ t ≫ boundaryPrecomp W = b := by
  letI : Fibration (boundaryPrecomp W) := boundaryPrecomp_fibration W hW
  haveI : Cofibration i :=
    (SSet.modelCategoryQuillen.cofibration_iff _).mpr inferInstance
  let sq : CommSq stationary i (boundaryPrecomp W) b := ⟨h⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- A compatible full boundary has a row-two filler stationary on the support. -/
theorem exists_row_filler (W : Source) {U : SSet.{0}} {k : SimplexCategory}
    (i : U ⟶ std.obj k) [Mono i] [WeakEquivalence i]
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (z : (row W ⦋0⦌).obj (op ⦋0⦌))
    (b : std.obj k ⟶ boundaryMapping W)
    (h : stationaryMapping W z ≫ boundaryPrecomp W = i ≫ b) :
    ∃ τ : std.obj k ⟶ row W ⦋2⦌,
      i ≫ τ = term U ≫ vertexPoint W z ≫ identityTriangle W ∧
        τ ≫ (fullRowIso W).inv ≫ boundaryPrecomp W = b := by
  obtain ⟨t, ht, hb⟩ := exists_mapping_filler W i hW (stationaryMapping W z) b h
  refine ⟨t ≫ (fullRowIso W).hom, ?_, ?_⟩
  · rw [← Category.assoc, ht, stationaryMapping_row]
  · calc
      (t ≫ (fullRowIso W).hom) ≫ (fullRowIso W).inv ≫ boundaryPrecomp W =
          t ≫ ((fullRowIso W).hom ≫ (fullRowIso W).inv) ≫
            boundaryPrecomp W := by simp only [Category.assoc]
      _ = t ≫ boundaryPrecomp W := by
        simp only [Iso.hom_inv_id, Category.id_comp]
      _ = b := hb

/-- A boundary filler has exactly the specified three genuine row-one edges
whenever the boundary face maps recover the ordinary simplex faces. -/
theorem exists_row_filler_edges (W : Source) {U : SSet.{0}} {k : SimplexCategory}
    (i : U ⟶ std.obj k) [Mono i] [WeakEquivalence i]
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (z : (row W ⦋0⦌).obj (op ⦋0⦌))
    (b : std.obj k ⟶ boundaryMapping W)
    (h : stationaryMapping W z ≫ boundaryPrecomp W = i ≫ b)
    (β : Fin 3 → (boundaryMapping W ⟶
      diagramMappingSpace (discreteFree.obj (Δ[1] : SSet.{0})) W))
    (hβ : ∀ j, boundaryPrecomp W ≫ β j = fullEdgePrecomp W j)
    (edges : Fin 3 → (std.obj k ⟶ row W ⦋1⦌))
    (he : ∀ j, b ≫ β j ≫
      (OrderedSimplexEndpointFiber.freeSimplexRowIso W 1).hom = edges j) :
    ∃ τ : std.obj k ⟶ row W ⦋2⦌,
      i ≫ τ = term U ≫ vertexPoint W z ≫ identityTriangle W ∧
        (∀ j, τ ≫ rowEdge W j = edges j) := by
  obtain ⟨τ, hτ, hb⟩ := exists_row_filler W i hW z b h
  refine ⟨τ, hτ, ?_⟩
  intro j
  calc
    τ ≫ rowEdge W j =
        τ ≫ (fullRowIso W).inv ≫ fullEdgePrecomp W j ≫
          (OrderedSimplexEndpointFiber.freeSimplexRowIso W 1).hom := by
      rw [← fullEdgePrecomp_row]
    _ = τ ≫ (fullRowIso W).inv ≫ boundaryPrecomp W ≫ β j ≫
          (OrderedSimplexEndpointFiber.freeSimplexRowIso W 1).hom := by
      simpa only [Category.assoc] using congrArg
        (fun g ↦ (τ ≫ (fullRowIso W).inv) ≫ g ≫
          (OrderedSimplexEndpointFiber.freeSimplexRowIso W 1).hom) (hβ j).symm
    _ = b ≫ β j ≫
          (OrderedSimplexEndpointFiber.freeSimplexRowIso W 1).hom := by
      simpa only [Category.assoc] using congrArg
        (fun g ↦ g ≫ β j ≫
          (OrderedSimplexEndpointFiber.freeSimplexRowIso W 1).hom) hb
    _ = edges j := he j

/-- Three compatible row-one edges, stationary on the relative support,
bound an actual row-two simplex with precisely those three faces. -/
theorem exists_boundary_triangle (W : Source) {U : SSet.{0}} {k : SimplexCategory}
    (i : U ⟶ std.obj k) [Mono i] [WeakEquivalence i]
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (z : (row W ⦋0⦌).obj (op ⦋0⦌))
    (D : JTTriangleBoundaryLabel.BoundaryData W k)
    (hD : ∀ j, i ≫ D.edge j = JTJointSubcomplexRelativeLift.identityOnU W z) :
    ∃ τ : std.obj k ⟶ row W ⦋2⦌,
      i ≫ τ = term U ≫ vertexPoint W z ≫ identityTriangle W ∧
        (∀ j, τ ≫ rowEdge W j = D.edge j) := by
  let b := JTTriangleBoundaryLabel.boundaryLabel D
  have hboundary : stationaryMapping W z ≫ boundaryPrecomp W = i ≫ b := by
    apply JTTriangleBoundaryLabel.boundaryLabel_ext_general
    intro j
    apply (cancel_mono (OrderedSimplexEndpointFiber.freeSimplexRowIso W 1).hom).mp
    calc
      (stationaryMapping W z ≫ boundaryPrecomp W ≫
          JTTriangleBoundaryLabel.facePrecomp W j) ≫
          (OrderedSimplexEndpointFiber.freeSimplexRowIso W 1).hom =
        JTJointSubcomplexRelativeLift.identityOnU W z := by
          have hface : boundaryPrecomp W ≫
              JTTriangleBoundaryLabel.facePrecomp W j =
                fullEdgePrecomp W j :=
            JTTriangleBoundaryLabel.full_facePrecomp W j
          have hh := congrArg
            (fun g ↦ stationaryMapping W (U := U) z ≫ g ≫
              (OrderedSimplexEndpointFiber.freeSimplexRowIso W 1).hom) hface
          simpa only [Category.assoc] using hh.trans (stationaryMapping_edge W z j)
      _ = i ≫ D.edge j := (hD j).symm
      _ = ((i ≫ b) ≫ JTTriangleBoundaryLabel.facePrecomp W j) ≫
            (OrderedSimplexEndpointFiber.freeSimplexRowIso W 1).hom := by
          simpa only [b, Category.assoc] using
            congrArg (fun g ↦ i ≫ g)
              (JTTriangleBoundaryLabel.boundaryLabel_face D j).symm
  exact exists_row_filler_edges W i hW z b hboundary
    (JTTriangleBoundaryLabel.facePrecomp W)
    (JTTriangleBoundaryLabel.full_facePrecomp W) D.edge
    (JTTriangleBoundaryLabel.boundaryLabel_face D)

private abbrev rows (W : Source) :=
  JTRealizationDiagonal.ordinaryCurry.obj (JTReversalInput.ordinaryInput.obj W)

/-- The relative pair of seam edges and the identity edge form the actual
three-sided boundary of an ordered two-simplex. -/
def seamBoundaryData (W : Source) {k : SimplexCategory}
    (f : std.obj k ⟶ row W ⦋0⦌)
    (z : (row W ⦋0⦌).obj (op ⦋0⦌))
    (e s : std.obj k ⟶ row W ⦋1⦌)
    (he : e ≫ JTProjectiveOrderedFiberComparison.endpointArrow W =
      JTJointSubcomplexRelativeLift.boundaryPair W f z)
    (hs : s ≫ JTProjectiveOrderedFiberComparison.endpointArrow W =
      JTJointSubcomplexRelativeLift.reverseBoundaryPair W f z) :
    JTTriangleBoundaryLabel.BoundaryData W k := by
  let edges : Fin 3 → (std.obj k ⟶ row W ⦋1⦌) :=
    ![s, f ≫ identityFamily W, e]
  apply JTTriangleBoundaryLabel.BoundaryData.ofEndpoints W k edges
  intro j l hjl
  have he₀ : e ≫ JTProjectiveOrderedFiberComparison.endpoint W 0 = f := by
    have h := congrArg (fun g ↦ g ≫ prod.fst) he
    simpa only [Category.assoc, JTProjectiveOrderedFiberComparison.endpointArrow,
      JTJointSubcomplexRelativeLift.boundaryPair, prod.lift_fst] using h
  have he₁ : e ≫ JTProjectiveOrderedFiberComparison.endpoint W 1 =
      term (std.obj k) ≫ vertexPoint W z := by
    have h := congrArg (fun g ↦ g ≫ prod.snd) he
    simpa only [Category.assoc, JTProjectiveOrderedFiberComparison.endpointArrow,
      JTJointSubcomplexRelativeLift.boundaryPair, prod.lift_snd] using h
  have hs₀ : s ≫ JTProjectiveOrderedFiberComparison.endpoint W 0 =
      term (std.obj k) ≫ vertexPoint W z := by
    have h := congrArg (fun g ↦ g ≫ prod.fst) hs
    simpa only [Category.assoc, JTProjectiveOrderedFiberComparison.endpointArrow,
      JTJointSubcomplexRelativeLift.reverseBoundaryPair, prod.lift_fst] using h
  have hs₁ : s ≫ JTProjectiveOrderedFiberComparison.endpoint W 1 = f := by
    have h := congrArg (fun g ↦ g ≫ prod.snd) hs
    simpa only [Category.assoc, JTProjectiveOrderedFiberComparison.endpointArrow,
      JTJointSubcomplexRelativeLift.reverseBoundaryPair, prod.lift_snd] using h
  fin_cases j <;> fin_cases l <;> simp at hjl
  · simp only [edges, Matrix.cons_val_zero', Matrix.cons_val_succ']
    have hcase : s ≫ JTProjectiveOrderedFiberComparison.endpoint W 1 =
        (f ≫ identityFamily W) ≫ JTProjectiveOrderedFiberComparison.endpoint W 1 := by
      rw [hs₁, Category.assoc, JTEndpointNormalizationLifts.identityFamily_endpoint,
        Category.comp_id]
    change s ≫ (rows W).map (SimplexCategory.δ (0 : Fin 2)).op =
      (f ≫ identityFamily W) ≫
        (rows W).map (SimplexCategory.δ (0 : Fin 2)).op
    rw [δ_zero_endpoint_one]
    exact hcase
  · simp only [edges, Matrix.cons_val_zero', Matrix.cons_val_succ']
    have hcase : s ≫ JTProjectiveOrderedFiberComparison.endpoint W 0 =
        e ≫ JTProjectiveOrderedFiberComparison.endpoint W 1 := hs₀.trans he₁.symm
    change s ≫ (rows W).map (SimplexCategory.δ (1 : Fin 2)).op =
      e ≫ (rows W).map (SimplexCategory.δ (0 : Fin 2)).op
    rw [δ_zero_endpoint_one, δ_one_endpoint_zero]
    exact hcase
  · simp only [edges, Matrix.cons_val_zero', Matrix.cons_val_succ']
    have hcase : (f ≫ identityFamily W) ≫
        JTProjectiveOrderedFiberComparison.endpoint W 0 =
          e ≫ JTProjectiveOrderedFiberComparison.endpoint W 0 := by
      rw [Category.assoc, JTEndpointNormalizationLifts.identityFamily_endpoint,
        Category.comp_id, he₀]
    change (f ≫ identityFamily W) ≫
        (rows W).map (SimplexCategory.δ (1 : Fin 2)).op =
          e ≫ (rows W).map (SimplexCategory.δ (1 : Fin 2)).op
    rw [δ_one_endpoint_zero]
    exact hcase

/-- The original relative edge pair admits a horizontal seam triangle.
Its `01`, `12`, and `02` edges are respectively the forward edge, the
reverse edge, and the literal identity edge of the variable row vertex. -/
theorem exists_seam_triangle (W : Source) {U : SSet.{0}} {k : SimplexCategory}
    (i : U ⟶ std.obj k) [Mono i] [WeakEquivalence i]
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (f : std.obj k ⟶ row W ⦋0⦌)
    (z : (row W ⦋0⦌).obj (op ⦋0⦌))
    (hf : i ≫ f = term U ≫ vertexPoint W z)
    (e s : std.obj k ⟶ row W ⦋1⦌)
    (hei : i ≫ e = JTJointSubcomplexRelativeLift.identityOnU W z)
    (hsi : i ≫ s = JTJointSubcomplexRelativeLift.identityOnU W z)
    (he : e ≫ JTProjectiveOrderedFiberComparison.endpointArrow W =
      JTJointSubcomplexRelativeLift.boundaryPair W f z)
    (hs : s ≫ JTProjectiveOrderedFiberComparison.endpointArrow W =
      JTJointSubcomplexRelativeLift.reverseBoundaryPair W f z) :
    ∃ τ : std.obj k ⟶ row W ⦋2⦌,
      i ≫ τ = term U ≫ vertexPoint W z ≫ identityTriangle W ∧
        τ ≫ rowEdge W 2 = e ∧
          τ ≫ rowEdge W 0 = s ∧
            τ ≫ rowEdge W 1 = f ≫ identityFamily W := by
  let D := seamBoundaryData W f z e s he hs
  have hD : ∀ j, i ≫ D.edge j =
      JTJointSubcomplexRelativeLift.identityOnU W z := by
    intro j
    fin_cases j
    · exact hsi
    · change i ≫ (f ≫ identityFamily W) =
        JTJointSubcomplexRelativeLift.identityOnU W z
      have hh := congrArg (fun g ↦ g ≫ identityFamily W) hf
      simpa only [Category.assoc, JTJointSubcomplexRelativeLift.identityOnU] using hh
    · exact hei
  obtain ⟨τ, hτ, hfaces⟩ := exists_boundary_triangle W i hW z D hD
  refine ⟨τ, hτ, ?_, ?_, ?_⟩
  · simpa only [D, seamBoundaryData, Matrix.cons_val_succ',
      Matrix.cons_val_zero'] using hfaces (2 : Fin 3)
  · simpa only [D, seamBoundaryData, Matrix.cons_val_zero'] using hfaces (0 : Fin 3)
  · simpa only [D, seamBoundaryData, Matrix.cons_val_succ',
      Matrix.cons_val_zero'] using hfaces (1 : Fin 3)

end
end DaggerModels.PartII.JTRelativeSeamTriangle
