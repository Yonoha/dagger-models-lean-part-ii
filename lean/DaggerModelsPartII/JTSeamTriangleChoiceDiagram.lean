import DaggerModelsPartII.JTVariableFixedLiftChoiceDiagram
import DaggerModelsPartII.JTRelativeSeamTriangle
import DaggerModelsPartII.JTTriangleBoundaryLabel
import DaggerModelsPartII.JTInterleavedParameter

/-! Natural higher choices of a relative seam triangle. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open MonoidalCategory CartesianMonoidalCategory
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSeamTriangleChoiceDiagram

open JTProjectiveOrderedFiberComparison (row vertexPoint endpointArrow)
open JTEndpointNormalizationLifts (identityFamily)
open JTJointSubcomplexRelativeLift (boundaryPair reverseBoundaryPair identityOnU)
open JTRelativeSeamTriangle (boundaryMapping boundaryPrecomp fullRowIso
  identityTriangle rowEdge)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

variable {I : Type} [SmallCategory I] (W : Source) (z : Vertex W)
variable (U : I ⥤ SSet.{0}) (K : I ⥤ SimplexCategory)
private abbrev Domain := K ⋙ std
variable (incl : U ⟶ Domain K)
variable (f : Domain K ⟶ (Functor.const I).obj (row W ⦋0⦌))
variable (e s : Domain K ⟶ (Functor.const I).obj (row W ⦋1⦌))
variable (he : ∀ a : I, e.app a ≫ endpointArrow W =
  boundaryPair W (f.app a) z)
variable (hs : ∀ a : I, s.app a ≫ endpointArrow W =
  reverseBoundaryPair W (f.app a) z)
variable (hfU : ∀ a : I, incl.app a ≫ f.app a =
  term (U.obj a) ≫ vertexPoint W z)
variable (heU : ∀ a : I, incl.app a ≫ e.app a = identityOnU W z)
variable (hsU : ∀ a : I, incl.app a ≫ s.app a = identityOnU W z)

/-- The literal three seam edges, opposite vertices zero, one, and two. -/
def edges (a : I) : Fin 3 → (std.obj (K.obj a) ⟶ row W ⦋1⦌) :=
  ![s.app a, f.app a ≫ identityFamily W, e.app a]

/-- The actual assembled boundary from the forward and reverse corrections. -/
def boundaryData (a : I) :
    JTTriangleBoundaryLabel.BoundaryData W (K.obj a) :=
  JTRelativeSeamTriangle.seamBoundaryData W (f.app a) z
    (e.app a) (s.app a) (he a) (hs a)

theorem boundaryData_edge (a : I) (j : Fin 3) :
    (boundaryData W z K f e s he hs a).edge j =
      edges W K f e s a j := by
  fin_cases j <;> rfl

theorem edges_map {a b : I} (q : a ⟶ b) (j : Fin 3) :
    edges W K f e s a j =
      (Domain K).map q ≫ edges W K f e s b j := by
  fin_cases j
  · exact (s.naturality q).symm
  · simpa only [edges, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Category.assoc] using congrArg (fun t ↦ t ≫ identityFamily W)
        (f.naturality q).symm
  · exact (e.naturality q).symm

/-- The exact naturally varying fixed-square problem for seam triangles. -/
def diagram : JTVariableFixedLiftChoiceDiagram.Diagram I where
  support := U
  domain := Domain K
  values := (Functor.const Iᵒᵖ).obj (row W ⦋2⦌)
  boundary := (Functor.const Iᵒᵖ).obj (boundaryMapping W)
  incl := incl
  restriction := (Functor.const Iᵒᵖ).map
    ((fullRowIso W).inv ≫ boundaryPrecomp W)
  onSupport a := term (U.obj a) ≫ vertexPoint W z ≫ identityTriangle W
  base a := JTTriangleBoundaryLabel.boundaryLabel
    (boundaryData W z K f e s he hs a)
  onSupport_map := by
    intro a b q
    change U.map q ≫
      (term (U.obj b) ≫ vertexPoint W z ≫ identityTriangle W) ≫ 𝟙 _ =
      term (U.obj a) ≫ vertexPoint W z ≫ identityTriangle W
    simp only [Category.comp_id]
    rw [← Category.assoc]
    congr 1
  base_map := by
    intro a b q
    change (Domain K).map q ≫
      JTTriangleBoundaryLabel.boundaryLabel
        (boundaryData W z K f e s he hs b) ≫ 𝟙 _ =
      JTTriangleBoundaryLabel.boundaryLabel
        (boundaryData W z K f e s he hs a)
    rw [Category.comp_id]
    apply (JTTriangleBoundaryLabel.boundaryLabel_natural
      (boundaryData W z K f e s he hs b)
      (boundaryData W z K f e s he hs a) (K.map q) ?_).symm
    intro j
    rw [boundaryData_edge, boundaryData_edge]
    exact edges_map W K f e s q j
  comm := by
    intro a
    change JTRelativeSeamTriangle.stationaryMapping W z ≫ boundaryPrecomp W =
      incl.app a ≫ JTTriangleBoundaryLabel.boundaryLabel
        (boundaryData W z K f e s he hs a)
    apply JTTriangleBoundaryLabel.boundaryLabel_ext_general
    intro j
    apply (cancel_mono
      (OrderedSimplexEndpointFiber.freeSimplexRowIso W 1).hom).mp
    calc
      (JTRelativeSeamTriangle.stationaryMapping W (U := U.obj a) z ≫
          boundaryPrecomp W ≫ JTTriangleBoundaryLabel.facePrecomp W j) ≫
          (OrderedSimplexEndpointFiber.freeSimplexRowIso W 1).hom =
        identityOnU W z := by
          have hface : boundaryPrecomp W ≫
              JTTriangleBoundaryLabel.facePrecomp W j =
                JTRelativeSeamTriangle.fullEdgePrecomp W j :=
            JTTriangleBoundaryLabel.full_facePrecomp W j
          have hh := congrArg
            (fun g ↦ JTRelativeSeamTriangle.stationaryMapping
              W (U := U.obj a) z ≫ g ≫
                (OrderedSimplexEndpointFiber.freeSimplexRowIso W 1).hom) hface
          simpa only [Category.assoc] using hh.trans
            (JTRelativeSeamTriangle.stationaryMapping_edge W z j)
      _ = incl.app a ≫ (boundaryData W z K f e s he hs a).edge j := by
        rw [boundaryData_edge]
        fin_cases j
        · exact (hsU a).symm
        · change identityOnU W z =
            incl.app a ≫ (f.app a ≫ identityFamily W)
          rw [← Category.assoc, hfU]
          rfl
        · exact (heU a).symm
      _ = ((incl.app a ≫ JTTriangleBoundaryLabel.boundaryLabel
          (boundaryData W z K f e s he hs a)) ≫
          JTTriangleBoundaryLabel.facePrecomp W j) ≫
          (OrderedSimplexEndpointFiber.freeSimplexRowIso W 1).hom := by
        simpa only [Category.assoc] using congrArg (fun g ↦ incl.app a ≫ g)
          (JTTriangleBoundaryLabel.boundaryLabel_face
            (boundaryData W z K f e s he hs a) j).symm

/-- Every higher coherent seam triangle choice, contravariant in the index. -/
abbrev spaces : Iᵒᵖ ⥤ SSet.{0} :=
  JTVariableFixedLiftChoiceDiagram.choices
    (diagram W z U K incl f e s he hs hfU heU hsU)

/-- The full time-dependent row-two label represented by any choice simplex. -/
def timeMap (a : I) (n : SimplexCategory)
    (x : (spaces W z U K incl f e s he hs hfU heU hsU).obj (op a) |>.obj (op n)) :
    std.obj (K.obj a) ⊗ std.obj n ⟶ row W ⦋2⦌ :=
  JTFixedLiftSpaceTimeEquiv.timeMap
    (JTVariableFixedLiftChoiceDiagram.square
      (diagram W z U K incl f e s he hs hfU heU hsU) a) n x

/-- The whole support is stationary for every higher triangle choice. -/
theorem timeMap_support (a : I) (n : SimplexCategory)
    (x : (spaces W z U K incl f e s he hs hfU heU hsU).obj (op a) |>.obj (op n)) :
    (incl.app a ▷ std.obj n) ≫ timeMap W z U K incl f e s he hs hfU heU hsU a n x =
      fst (U.obj a) (std.obj n) ≫
        (term (U.obj a) ≫ vertexPoint W z ≫ identityTriangle W) :=
  (JTFixedLiftSpaceTimeEquiv.timeMap_conditions
    (JTVariableFixedLiftChoiceDiagram.square
      (diagram W z U K incl f e s he hs hfU heU hsU) a) n x).1

/-- The entire boundary of each time-dependent triangle is prescribed. -/
theorem timeMap_boundary (a : I) (n : SimplexCategory)
    (x : (spaces W z U K incl f e s he hs hfU heU hsU).obj (op a) |>.obj (op n)) :
    timeMap W z U K incl f e s he hs hfU heU hsU a n x ≫
        (fullRowIso W).inv ≫ boundaryPrecomp W =
      fst (std.obj (K.obj a)) (std.obj n) ≫
        JTTriangleBoundaryLabel.boundaryLabel
          (boundaryData W z K f e s he hs a) :=
  (JTFixedLiftSpaceTimeEquiv.timeMap_conditions
    (JTVariableFixedLiftChoiceDiagram.square
      (diagram W z U K incl f e s he hs hfU heU hsU) a) n x).2

/-- Every simplex of the full choice diagram transports its entire time map. -/
theorem timeMap_natural {a b : I} (q : a ⟶ b) (n : SimplexCategory)
    (x : (spaces W z U K incl f e s he hs hfU heU hsU).obj (op b) |>.obj (op n)) :
    timeMap W z U K incl f e s he hs hfU heU hsU a n
        (((spaces W z U K incl f e s he hs hfU heU hsU).map q.op).app (op n) x) =
      ((Domain K).map q ▷ std.obj n) ≫
        timeMap W z U K incl f e s he hs hfU heU hsU b n x := by
  have h := JTVariableFixedLiftSpaceMap.timeMap_mapSquare
    (JTVariableFixedLiftChoiceDiagram.square
      (diagram W z U K incl f e s he hs hfU heU hsU) b)
    (JTVariableFixedLiftChoiceDiagram.square
      (diagram W z U K incl f e s he hs hfU heU hsU) a)
    (U.map q) ((Domain K).map q) (𝟙 _) (𝟙 _)
    (incl.naturality q)
    ((diagram W z U K incl f e s he hs hfU heU hsU).onSupport_map q)
    ((diagram W z U K incl f e s he hs hfU heU hsU).restriction.naturality q.op).symm
    ((diagram W z U K incl f e s he hs hfU heU hsU).base_map q) n x
  simpa only [spaces, timeMap, JTVariableFixedLiftChoiceDiagram.restrict,
    Category.comp_id] using h

/-- The same map also respects every simplex operator in the choice time. -/
theorem timeMap_time {m n : SimplexCategory} (α : m ⟶ n) (a : I)
    (x : (spaces W z U K incl f e s he hs hfU heU hsU).obj (op a) |>.obj (op n)) :
    timeMap W z U K incl f e s he hs hfU heU hsU a m
        (((spaces W z U K incl f e s he hs hfU heU hsU).obj (op a)).map α.op x) =
      (std.obj (K.obj a) ◁ std.map α) ≫
        timeMap W z U K incl f e s he hs hfU heU hsU a n x :=
  JTFixedLiftSpaceTimeEquiv.timeMap_map
    (JTVariableFixedLiftChoiceDiagram.square
      (diagram W z U K incl f e s he hs hfU heU hsU) a) α x

/-- The boundary map of every seam choice is a Kan fibration. -/
theorem restriction_fibration (hW : letI : ModelCategory Source :=
    InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (a : I) :
    Fibration ((diagram W z U K incl f e s he hs hfU heU hsU).restriction.app
      (op a)) := by
  change Fibration ((fullRowIso W).inv ≫ boundaryPrecomp W)
  haveI : Fibration ((fullRowIso W).inv) := inferInstance
  haveI : Fibration (boundaryPrecomp W) :=
    JTRelativeSeamTriangle.boundaryPrecomp_fibration W hW
  infer_instance

/-- Every all-dimensional seam filler space is Kan. -/
theorem spaces_kan (hi : ∀ a : I, Mono (incl.app a))
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (a : Iᵒᵖ) : ((spaces W z U K incl f e s he hs hfU heU hsU).obj a).KanComplex := by
  apply JTVariableFixedLiftChoiceDiagram.choices_kan
    (diagram W z U K incl f e s he hs hfU heU hsU) hi
  exact fun b ↦ restriction_fibration W z U K incl f e s he hs hfU heU hsU hW b

/-- Every all-dimensional seam filler fiber is weakly contractible. -/
theorem spaces_toPoint_weak (hi : ∀ a : I, Mono (incl.app a))
    (hw : ∀ a : I, WeakEquivalence (incl.app a))
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (a : Iᵒᵖ) :
    WeakEquivalence (term ((spaces W z U K incl f e s he hs hfU heU hsU).obj a)) := by
  apply JTVariableFixedLiftChoiceDiagram.choices_toPoint_weak
    (diagram W z U K incl f e s he hs hfU heU hsU) hi hw
  exact fun b ↦ restriction_fibration W z U K incl f e s he hs hfU heU hsU hW b

/-- Total simplices of seam choices give a weak cover of the original index. -/
theorem projection_weak (hi : ∀ a : I, Mono (incl.app a))
    (hw : ∀ a : I, WeakEquivalence (incl.app a))
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence (nerveMap
      (JTVariableFixedLiftChoiceDiagram.projection
        (diagram W z U K incl f e s he hs hfU heU hsU))) := by
  apply JTVariableFixedLiftChoiceDiagram.projection_weak
    (diagram W z U K incl f e s he hs hfU heU hsU) hi hw
  exact fun b ↦ restriction_fibration W z U K incl f e s he hs hfU heU hsU hW b

end
end DaggerModels.PartII.JTSeamTriangleChoiceDiagram
