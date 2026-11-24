import DaggerModelsPartII.JTMixedGraphEdgeFamilyReindex
import DaggerModelsPartII.JTHigherEndpointExtension
import DaggerModelsPartII.JTHigherInterleavedOperators
import DaggerModelsPartII.JTCommonCoefficientLiftChoices

/-!
# Common ordered-label coefficients for a full time boundary
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra
  CartesianMonoidalCategory DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTHigherCommonMixedGraphFamilies

open JTProjectiveOrderedFiberComparison JTMixedGraphEndpointLifts
open JTHigherInterleavedParameter JTMixedGraphEdgeFamilyReindex
open JTEndpointNormalizationLifts

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev simplex (k : SimplexCategory) := SSet.stdSimplex.{0}.obj k
private abbrev J := GroupoidSimplex.parameter
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev bd (n : ℕ) : SSet.{0} := SSet.boundary n
private abbrev bdι (n : ℕ) : bd n ⟶ simplex ⦋n⦌ := (SSet.boundary n).ι
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

/-- A full prescribed time boundary for one outside row, over the fixed
ordered pair of endpoints and stationary at the selected parameter vertex. -/
structure SideBoundary (W : Source) (k : SimplexCategory) (n : ℕ)
    (a : Fin (k.len + 1)) (b : simplex k ⟶ row W ⦋0⦌ ⨯ row W ⦋0⦌)
    (t : simplex ⦋0⦌ ⟶ row W ⦋1⦌) where
  map : simplex k ⊗ bd n ⟶ row W ⦋1⦌
  over : map ≫ endpointArrow W =
    (simplex k ◁ bdι n) ≫ fst (simplex k) (simplex ⦋n⦌) ≫ b
  stationary : (vertex k a ▷ bd n) ≫ map =
    (simplex ⦋0⦌ ◁ bdι n) ≫ fst (simplex ⦋0⦌) (simplex ⦋n⦌) ≫ t

private theorem verticalSection_vertex (k n : SimplexCategory) (a : Fin (k.len + 1)) :
    lift (term (simplex n)) (𝟙 (simplex n)) ≫ (vertex k a ▷ simplex n) =
      verticalSection k n a := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, whiskerRight_fst, lift_fst_assoc, verticalSection, lift_fst]
    have h : term (simplex n) =
        SSet.stdSimplex.map (SimplexCategory.const n ⦋0⦌ 0) :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [h, vertex, ← SSet.stdSimplex.map_comp, SimplexCategory.const_comp]
    rfl
  · simp only [verticalSection, Category.assoc, whiskerRight_snd, lift_snd]

private theorem exists_side_extension (W : Source)
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (k : SimplexCategory) (n : ℕ) (a : Fin (k.len + 1))
    (b : simplex k ⟶ row W ⦋0⦌ ⨯ row W ⦋0⦌) (t : simplex ⦋0⦌ ⟶ row W ⦋1⦌)
    (ht : t ≫ endpointArrow W = vertex k a ≫ b)
    (g : SideBoundary W k n a b t) :
    ∃ E : simplex (common k ⦋n⦌) ⟶ row W ⦋1⦌,
      (simplex k ◁ bdι n) ≫ prism k ⦋n⦌ ≫ E = g.map ∧
      SSet.stdSimplex.map (vertical k ⦋n⦌ a) ≫ E = term (simplex ⦋n⦌) ≫ t ∧
      E ≫ endpointArrow W = SSet.stdSimplex.map (ret k ⦋n⦌) ≫ b := by
  letI : Mono (vertex k a) := SSet.stdSimplex.isTerminalObj₀.mono_from _
  letI : WeakEquivalence (vertex k a) := JTInterleavedParameter.standardMap_weak _
  have hA : (fst (simplex ⦋0⦌) (simplex ⦋n⦌) ≫ t) ≫ endpointArrow W =
      (vertex k a ▷ simplex ⦋n⦌) ≫ fst (simplex k) (simplex ⦋n⦌) ≫ b := by
    rw [Category.assoc, ht, whiskerRight_fst_assoc]
  obtain ⟨E, hBd, hA, hBase⟩ := JTHigherEndpointExtension.exists_boundary_extension
    k n W hW (vertex k a) b g.map (fst (simplex ⦋0⦌) (simplex ⦋n⦌) ≫ t)
    g.stationary g.over hA
  refine ⟨E, hBd, ?_, hBase⟩
  rw [← verticalSection_prism, ← verticalSection_vertex, Category.assoc, Category.assoc, hA,
    lift_fst_assoc]

private theorem vertex_slice_vertical (k n : SimplexCategory) (a : Fin (k.len + 1))
    (t : Fin (n.len + 1)) :
    vertex (common k n) ((slice k n t).toOrderHom a) =
      vertex n t ≫ SSet.stdSimplex.map (vertical k n a) := by
  unfold vertex
  rw [← SSet.stdSimplex.map_comp, SimplexCategory.const_comp]
  rfl

private abbrev leftBase {W : Source} {d : ℕ} {k : SimplexCategory}
    (f : simplex k ⟶ row W ⦋d⦌) (x : (row W ⦋0⦌).obj (op ⦋0⦌)) :=
  prod.lift (term (simplex k) ≫ vertexPoint W x) (f ≫ rowVertex W ⦋d⦌ 0)

private abbrev rightBase {W : Source} {d : ℕ} {k : SimplexCategory}
    (f : simplex k ⟶ row W ⦋d⦌) (y : (row W ⦋0⦌).obj (op ⦋0⦌)) :=
  prod.lift (f ≫ rowVertex W ⦋d⦌ (Fin.last d)) (term (simplex k) ≫ vertexPoint W y)

private abbrev identityAt {W : Source} (z : (row W ⦋0⦌).obj (op ⦋0⦌)) :=
  vertexPoint W z ≫ identityFamily W

private theorem leftBase_precomp {W : Source} {d : ℕ} {k l : SimplexCategory}
    (j : k ⟶ l) (f : simplex l ⟶ row W ⦋d⦌) (x : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    SSet.stdSimplex.map j ≫ leftBase f x = leftBase (SSet.stdSimplex.map j ≫ f) x := by
  apply prod.hom_ext
  · simp only [leftBase, Category.assoc, prod.lift_fst]
    have h : SSet.stdSimplex.map j ≫ term (simplex l) = term (simplex k) :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [← Category.assoc, h]
  · simp only [leftBase, Category.assoc, prod.lift_snd]

private theorem rightBase_precomp {W : Source} {d : ℕ} {k l : SimplexCategory}
    (j : k ⟶ l) (f : simplex l ⟶ row W ⦋d⦌) (y : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    SSet.stdSimplex.map j ≫ rightBase f y = rightBase (SSet.stdSimplex.map j ≫ f) y := by
  apply prod.hom_ext
  · simp only [rightBase, Category.assoc, prod.lift_fst]
  · simp only [rightBase, Category.assoc, prod.lift_snd]
    have h : SSet.stdSimplex.map j ≫ term (simplex l) = term (simplex k) :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [← Category.assoc, h]

/-- Prescriptions for both outside coefficients of the actual three-bead
ordered label, with the middle coefficient held fixed. -/
structure BoundaryFamilies (W : Source) (d : ℕ) (k : SimplexCategory) (n : ℕ)
    (f : simplex k ⟶ row W ⦋d⦌) (s : simplex ⦋d⦌ ⟶ J.obj k)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) where
  left : SideBoundary W k n (graphIndex ⦋d⦌ k s 0) (leftBase f x) (identityAt x)
  right : SideBoundary W k n (graphIndex ⦋d⦌ k s (Fin.last d)) (rightBase f y) (identityAt y)

set_option maxHeartbeats 600000 in
/-- Extend both complete prescribed boundaries to the same coefficient of
the original mixed graph. The entire two vertical simplices are identities.
The raw endpoint equations supply the original stationary endpoint data. -/
theorem exists_commonFamilies {W : Source}
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (d : ℕ) (k : SimplexCategory) (n : ℕ)
    (f : simplex k ⟶ row W ⦋d⦌) (s : simplex ⦋d⦌ ⟶ J.obj k)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
    (hx : SSet.yonedaEquiv (vertex ⦋d⦌ 0 ≫ rawGraph W ⦋d⦌ k f s) = rawVertex W x)
    (hy : SSet.yonedaEquiv (vertex ⦋d⦌ (Fin.last d) ≫ rawGraph W ⦋d⦌ k f s) = rawVertex W y)
    (g : BoundaryFamilies W d k n f s x y) :
    ∃ E : EdgeFamilies W ⦋d⦌ (common k ⦋n⦌)
        (SSet.stdSimplex.map (ret k ⦋n⦌) ≫ f) (s ≫ J.map (slice k ⦋n⦌ 0)) x y,
      (simplex k ◁ bdι n) ≫ prism k ⦋n⦌ ≫ E.left = g.left.map ∧
      (simplex k ◁ bdι n) ≫ prism k ⦋n⦌ ≫ E.right = g.right.map ∧
      SSet.stdSimplex.map (vertical k ⦋n⦌ (graphIndex ⦋d⦌ k s 0)) ≫ E.left =
        term (simplex ⦋n⦌) ≫ identityAt x ∧
      SSet.stdSimplex.map (vertical k ⦋n⦌ (graphIndex ⦋d⦌ k s (Fin.last d))) ≫ E.right =
        term (simplex ⦋n⦌) ≫ identityAt y := by
  let e := chosenEdgeFamilies W hW ⦋d⦌ k f s x y hx hy
  let a := graphIndex ⦋d⦌ k s 0
  let b := graphIndex ⦋d⦌ k s (Fin.last d)
  have hL : identityAt x ≫ endpointArrow W = vertex k a ≫ leftBase f x := by
    calc
      _ = (vertex k a ≫ e.left) ≫ endpointArrow W :=
        congrArg (fun u ↦ u ≫ endpointArrow W) e.left_degenerate.symm
      _ = _ := by rw [Category.assoc, e.left_boundary]
  have hR : identityAt y ≫ endpointArrow W = vertex k b ≫ rightBase f y := by
    calc
      _ = (vertex k b ≫ e.right) ≫ endpointArrow W :=
        congrArg (fun u ↦ u ≫ endpointArrow W) e.right_degenerate.symm
      _ = _ := by
        rw [Category.assoc, e.right_boundary]
        rfl
  obtain ⟨L, hLb, hLv, hLp⟩ := exists_side_extension W hW k n a
    (leftBase f x) (identityAt x) hL g.left
  obtain ⟨R, hRb, hRv, hRp⟩ := exists_side_extension W hW k n b
    (rightBase f y) (identityAt y) hR g.right
  refine ⟨{
    left := L
    right := R
    left_boundary := hLp.trans (leftBase_precomp (ret k ⦋n⦌) f x)
    right_boundary := hRp.trans (rightBase_precomp (ret k ⦋n⦌) f y)
    left_degenerate := ?_
    right_degenerate := ?_ }, hLb, hRb, hLv, hRv⟩
  · rw [graphIndex_reindex, vertex_slice_vertical, Category.assoc, hLv]
    rw [← Category.assoc, SSet.stdSimplex.isTerminalObj₀.hom_ext
      (vertex ⦋n⦌ 0 ≫ term (simplex ⦋n⦌)) (𝟙 _), Category.id_comp]
  · rw [graphIndex_reindex, vertex_slice_vertical, Category.assoc]
    change vertex ⦋n⦌ 0 ≫ SSet.stdSimplex.map (vertical k ⦋n⦌ b) ≫ R = identityAt y
    rw [hRv]
    rw [← Category.assoc, SSet.stdSimplex.isTerminalObj₀.hom_ext
      (vertex ⦋n⦌ 0 ≫ term (simplex ⦋n⦌)) (𝟙 _), Category.id_comp]

/-- A time operator that factors through the boundary retains the entire
prescribed product map in that degree. -/
theorem restrict_to_time_operator {k m : SimplexCategory} {n : ℕ} {X : SSet.{0}}
    (j : m ⟶ ⦋n⦌) (v : simplex m ⟶ bd n)
    (hv : v ≫ bdι n = SSet.stdSimplex.map j)
    (E : simplex (common k ⦋n⦌) ⟶ X) (g : simplex k ⊗ bd n ⟶ X)
    (hE : (simplex k ◁ bdι n) ≫ prism k ⦋n⦌ ≫ E = g) :
    prism k m ≫ SSet.stdSimplex.map (mapTime k j) ≫ E = (simplex k ◁ v) ≫ g := by
  rw [← Category.assoc, prism_mapTime, Category.assoc, ← hv,
    whiskerLeft_comp, Category.assoc, hE]

open JTCommonCoefficientLiftChoices (Extension)

/-- The entire enlarged time simplex at the prescribed endpoint is stationary. -/
theorem common_vertical_stationary {k b n : SimplexCategory} (c : k ⟶ b)
    {X Y : SSet.{0}} {p : X ⟶ Y} {g : simplex b ⟶ Y} {t : simplex ⦋0⦌ ⟶ X}
    (a : Fin (k.len + 1))
    (sq : CommSq t (vertex k a) p (SSet.stdSimplex.map c ≫ g))
    (E : Extension sq n) :
    SSet.stdSimplex.map (JTCommonCoefficientParameter.vertical c n a) ≫ E.map =
      term (simplex n) ≫ t := by
  rw [← JTCommonCoefficientParameter.verticalSection_prism,
    ← verticalSection_vertex, Category.assoc, Category.assoc, E.stationary, lift_fst_assoc]

private theorem common_vertex_slice_vertical {k b : SimplexCategory} (c : k ⟶ b)
    (n : SimplexCategory) (a : Fin (k.len + 1)) (t : Fin (n.len + 1)) :
    vertex (common k n) ((JTCommonCoefficientParameter.slice c n t).toOrderHom a) =
      vertex n t ≫ SSet.stdSimplex.map (JTCommonCoefficientParameter.vertical c n a) := by
  unfold vertex
  rw [← SSet.stdSimplex.map_comp, SimplexCategory.const_comp]
  rfl

private theorem common_degenerate {k b n : SimplexCategory} (c : k ⟶ b)
    {X Y : SSet.{0}} {p : X ⟶ Y} {g : simplex b ⟶ Y} {t : simplex ⦋0⦌ ⟶ X}
    (a : Fin (k.len + 1))
    (sq : CommSq t (vertex k a) p (SSet.stdSimplex.map c ≫ g))
    (E : Extension sq n) (v : Fin (n.len + 1)) :
    vertex (common k n) ((JTCommonCoefficientParameter.slice c n v).toOrderHom a) ≫
      E.map = t := by
  rw [common_vertex_slice_vertical, Category.assoc, common_vertical_stationary c a sq E,
    ← Category.assoc, SSet.stdSimplex.isTerminalObj₀.hom_ext
      (vertex n v ≫ term (simplex n)) (𝟙 _), Category.id_comp]

section Ordered

variable {W : Source} {d : ℕ} {k b : SimplexCategory}
variable (c : k ⟶ b) (n : SimplexCategory)
variable (f : simplex b ⟶ row W ⦋d⦌) (s : simplex ⦋d⦌ ⟶ J.obj k)
variable (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
variable {sqL : CommSq (identityAt x) (vertex k (graphIndex ⦋d⦌ k s 0)) (endpointArrow W)
    (SSet.stdSimplex.map c ≫ leftBase f x)}
variable {sqR : CommSq (identityAt y) (vertex k (graphIndex ⦋d⦌ k s (Fin.last d)))
    (endpointArrow W) (SSet.stdSimplex.map c ≫ rightBase f y)}
variable (L : Extension sqL n) (R : Extension sqR n)

/-- The given common-coefficient choices supply the complete original
ordered edge families at any time slice. -/
def commonChoiceFamilies (v : Fin (n.len + 1)) :
    EdgeFamilies W ⦋d⦌ (common k n)
      (SSet.stdSimplex.map (JTCommonCoefficientParameter.base c n) ≫ f)
      (s ≫ J.map (JTCommonCoefficientParameter.slice c n v)) x y where
  left := L.map
  right := R.map
  left_boundary := L.over.trans (leftBase_precomp (JTCommonCoefficientParameter.base c n) f x)
  right_boundary := R.over.trans (rightBase_precomp (JTCommonCoefficientParameter.base c n) f y)
  left_degenerate := by
    rw [graphIndex_reindex]
    exact common_degenerate c _ sqL L v
  right_degenerate := by
    rw [graphIndex_reindex]
    exact common_degenerate c (graphIndex ⦋d⦌ k s (Fin.last d)) sqR R v

/-- The time-slice witness only checks the degenerate ends. The three maps
defining the native ordered label are independent of that witness. -/
theorem commonChoiceFamilies_orderedPoint {v w : Fin (n.len + 1)} :
    JTMixedGraphOrderedLabel.orderedPoint (commonChoiceFamilies c n f s x y L R v) =
      JTMixedGraphOrderedLabel.orderedPoint (commonChoiceFamilies c n f s x y L R w) := by
  let a := JTMixedGraphOrderedLabel.families (commonChoiceFamilies c n f s x y L R w)
  let b := JTMixedGraphOrderedLabel.families (commonChoiceFamilies c n f s x y L R v)
  let K := common k n
  let F := (OrderedNecklaceLabelDiagram.orderedNecklaceLabels W
    (OrderedNecklaceVertexPoints.boundaryPoint W x y)).obj
      (op (TripleBeadEndpointLabel.code d))
  have hleft : b.left = SSet.stdSimplex.map (𝟙 K) ≫ a.left := by
    rw [SSet.stdSimplex.{0}.map_id K, Category.id_comp]
    rfl
  have hmiddle : b.middle = SSet.stdSimplex.map (𝟙 K) ≫ a.middle := by
    rw [SSet.stdSimplex.{0}.map_id K, Category.id_comp]
    rfl
  have hright : b.right = SSet.stdSimplex.map (𝟙 K) ≫ a.right := by
    rw [SSet.stdSimplex.{0}.map_id K, Category.id_comp]
    rfl
  have h := orderedPoint_reindex_of_rows (𝟙 K) a b hleft hmiddle hright
  change TripleBeadEndpointLabel.orderedPoint b =
    F.map (𝟙 K).op (TripleBeadEndpointLabel.orderedPoint a) at h
  rw [op_id, F.map_id] at h
  exact h


variable {l m : SimplexCategory} (c' : l ⟶ b) (s' : simplex ⦋d⦌ ⟶ J.obj l)
variable {sqL' : CommSq (identityAt x) (vertex l (graphIndex ⦋d⦌ l s' 0)) (endpointArrow W)
    (SSet.stdSimplex.map c' ≫ leftBase f x)}
variable {sqR' : CommSq (identityAt y) (vertex l (graphIndex ⦋d⦌ l s' (Fin.last d)))
    (endpointArrow W) (SSet.stdSimplex.map c' ≫ rightBase f y)}
variable (L' : Extension sqL' m) (R' : Extension sqR' m)

/-- The original ordered label restricts along the simultaneous common-base
coefficient and injective time operator. The two time-slice witnesses are free. -/
theorem commonChoiceFamilies_orderedPoint_reindex
    (a : k ⟶ l) (ha : a ≫ c' = c) (j : n ⟶ m) (hj : Function.Injective j.toOrderHom)
    (v : Fin (n.len + 1)) (w : Fin (m.len + 1))
    (hL : L.map = SSet.stdSimplex.map
      (JTCommonCoefficientParameter.map a ha j hj) ≫ L'.map)
    (hR : R.map = SSet.stdSimplex.map
      (JTCommonCoefficientParameter.map a ha j hj) ≫ R'.map) :
    JTMixedGraphOrderedLabel.orderedPoint (commonChoiceFamilies c n f s x y L R v) =
      ((OrderedNecklaceLabelDiagram.orderedNecklaceLabels W
        (OrderedNecklaceVertexPoints.boundaryPoint W x y)).obj
        (op (TripleBeadEndpointLabel.code d))).map
          (JTCommonCoefficientParameter.map a ha j hj).op
          (JTMixedGraphOrderedLabel.orderedPoint (commonChoiceFamilies c' m f s' x y L' R' w)) := by
  let u := JTCommonCoefficientParameter.map a ha j hj
  let Q := JTMixedGraphOrderedLabel.families (commonChoiceFamilies c n f s x y L R v)
  let Q' := JTMixedGraphOrderedLabel.families (commonChoiceFamilies c' m f s' x y L' R' w)
  apply orderedPoint_reindex_of_rows u Q' Q
  · change L.map ≫ _ = SSet.stdSimplex.map u ≫ L'.map ≫ _
    rw [← Category.assoc, ← hL]
  · change (SSet.stdSimplex.map (JTCommonCoefficientParameter.base c n) ≫ f) ≫ _ =
      SSet.stdSimplex.map u ≫
        (SSet.stdSimplex.map (JTCommonCoefficientParameter.base c' m) ≫ f) ≫ _
    rw [← Category.assoc (SSet.stdSimplex.map u), ← Category.assoc
      (SSet.stdSimplex.map u), ← SSet.stdSimplex.map_comp]
    rw [JTCommonCoefficientParameter.map_base a ha j hj]
  · change R.map ≫ _ = SSet.stdSimplex.map u ≫ R'.map ≫ _
    rw [← Category.assoc, ← hR]

end Ordered

end
end DaggerModels.PartII.JTHigherCommonMixedGraphFamilies
