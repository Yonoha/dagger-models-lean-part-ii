import DaggerModelsPartII.JTMixedGraphRawRefinement

/-!
# Horizontal compatibility of the actual padded graph traversal

An endpoint-preserving horizontal simplex operator is allowed to collapse
vertices. Its extension to the three-bead graph preserves both outer beads
and commutes with the full collapse and parameter, in all degrees.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTMixedGraphHorizontalTraversal

open MixedGraphCylinderTraversal JTMixedGraphEndpointLifts JTMixedGraphRawRefinement

noncomputable section

private abbrev A := single 1
private abbrev Δ (n : SimplexCategory) := SSet.stdSimplex.{0}.obj n
private abbrev J := GroupoidSimplex.parameter
private abbrev L (d : ℕ) := tripleRightT.{0} A (single d) A
private abbrev M (d : ℕ) := tripleRightU.{0} A (single d) A
private abbrev R (d : ℕ) := tripleRightV.{0} A (single d) A

variable {d e f : ℕ}

/-- Add the same first and last bead to an original middle-bead operator. -/
def padded (u : single d ⟶ single e) : code d ⟶ code e :=
  wedgeMap (𝟙 A) (wedgeMap u (𝟙 A))

theorem padded_left (u : single d ⟶ single e) : L d ≫ (padded u).map = L e := by
  simp only [L, tripleRightT, padded, wedgeMap_left]
  exact Category.id_comp _

theorem padded_middle (u : single d ⟶ single e) : M d ≫ (padded u).map = u.map ≫ M e := by
  unfold M padded tripleRightU
  rw [Category.assoc, wedgeMap_right, ← Category.assoc, wedgeMap_left, Category.assoc]

theorem padded_right (u : single d ⟶ single e) : R d ≫ (padded u).map = R e := by
  unfold R padded tripleRightV
  rw [Category.assoc, wedgeMap_right, ← Category.assoc, wedgeMap_right]
  change (𝟙 A.toSSet ≫ wedgeιRight (single e) A) ≫
    wedgeιRight A (wedge (single e) A) = _
  rw [Category.id_comp]

theorem padded_comp (u : NecklaceCode.Hom.{0} (single d) (single e))
    (v : NecklaceCode.Hom.{0} (single e) (single f)) :
    padded u ≫ padded v = padded (u ≫ v) := by
  apply Hom.ext
  change (padded u).map ≫ (padded v).map = (padded (u ≫ v)).map
  apply tripleRight_hom_ext (T := A) (U := single d) (V := A)
  · change L d ≫ ((padded u).map ≫ (padded v).map) = L d ≫ (padded (u ≫ v)).map
    rw [← Category.assoc, padded_left, padded_left, padded_left]
  · change M d ≫ ((padded u).map ≫ (padded v).map) = M d ≫ (padded (u ≫ v)).map
    rw [← Category.assoc, padded_middle, Category.assoc, padded_middle, padded_middle]
    exact (Category.assoc _ _ _).symm
  · change R d ≫ ((padded u).map ≫ (padded v).map) = R d ≫ (padded (u ≫ v)).map
    rw [← Category.assoc, padded_right, padded_right, padded_right]

/-- The full native collapse to the actual middle bead is natural. -/
theorem collapse_natural (u : single d ⟶ single e) :
    padded u ≫ collapseOuter e = collapseOuter d ≫ u := by
  apply Hom.ext
  change (padded u).map ≫ collapseMap e = collapseMap d ≫ u.map
  apply tripleRight_hom_ext (T := A) (U := single d) (V := A)
  · rw [← Category.assoc, padded_left, collapseMap_left, ← Category.assoc,
      collapseMap_left, Category.assoc, pointAt_first_comp]
  · rw [← Category.assoc, padded_middle, Category.assoc, collapseMap_middle,
      ← Category.assoc (M d), collapseMap_middle, Category.comp_id, Category.id_comp]
  · rw [← Category.assoc, padded_right, collapseMap_right, ← Category.assoc,
      collapseMap_right, Category.assoc, pointAt_last_comp]

/-- The full parameter on the padded graph factors through its native middle bead. -/
theorem parameter_factor {k : SimplexCategory} (s : Δ ⦋d⦌ ⟶ J.obj k) :
    nativeGraphParameter s = collapseMap d ≫ (singleIso d).hom ≫ s := by
  unfold nativeGraphParameter
  apply tripleRight_hom_ext (T := A) (U := single d) (V := A)
  · rw [graphParameter_left, ← Category.assoc, collapseMap_left]
    unfold constantParameter
    rw [Category.assoc, ← Category.assoc (pointAt (single d) (ULift.up 0)),
      JTNativeRowLabel.nativeVertex, graphIndex_vertex]
  · rw [graphParameter_middle, ← Category.assoc, collapseMap_middle, Category.id_comp]
  · rw [graphParameter_right, ← Category.assoc, collapseMap_right]
    change _ = SSet.stdSimplex.isTerminalObj₀.from A.toSSet ≫
      pointAt (single d) (ULift.up (Fin.last d)) ≫ (singleIso d).hom ≫ s
    rw [← Category.assoc (pointAt (single d) (ULift.up (Fin.last d))),
      JTNativeRowLabel.nativeVertex, graphIndex_vertex]
    rfl

private theorem vertex_map (a : ⦋d⦌ ⟶ ⦋e⦌) (i : Fin (d + 1)) :
    vertex ⦋d⦌ i ≫ SSet.stdSimplex.map a = vertex ⦋e⦌ (a.toOrderHom i) := by
  unfold vertex
  rw [← SSet.stdSimplex.map_comp, SimplexCategory.const_comp]

/-- An endpoint-preserving simplex operator acts on the original one-bead necklace. -/
def singleOperator (a : ⦋d⦌ ⟶ ⦋e⦌)
    (h₀ : a.toOrderHom 0 = 0) (h₁ : a.toOrderHom (Fin.last d) = Fin.last e) :
    single d ⟶ single e where
  map := (singleIso d).hom ≫ SSet.stdSimplex.map a ≫ (singleIso e).inv
  first := first_of_point _ (by
    rw [← Category.assoc, ← Category.assoc, JTNativeRowLabel.nativeVertex, vertex_map,
      h₀, ← JTNativeRowLabel.nativeVertex, Category.assoc, Iso.hom_inv_id, Category.comp_id])
  last := last_of_point _ (by
    rw [← Category.assoc, ← Category.assoc, JTNativeRowLabel.nativeVertex, vertex_map]
    change vertex ⦋e⦌ (a.toOrderHom (Fin.last d)) ≫ (singleIso e).inv =
      pointAt (single e) (ULift.up (Fin.last e))
    rw [h₁, ← JTNativeRowLabel.nativeVertex, Category.assoc, Iso.hom_inv_id, Category.comp_id])

/-- Horizontal restriction commutes with the entire mixed graph parameter. -/
theorem parameter_horizontal {k : SimplexCategory} (a : ⦋d⦌ ⟶ ⦋e⦌)
    (h₀ : a.toOrderHom 0 = 0) (h₁ : a.toOrderHom (Fin.last d) = Fin.last e)
    (t : Δ ⦋e⦌ ⟶ J.obj k) :
    (padded (singleOperator a h₀ h₁)).map ≫ nativeGraphParameter t =
      nativeGraphParameter (SSet.stdSimplex.map a ≫ t) := by
  rw [parameter_factor, parameter_factor, ← Category.assoc]
  have h := congrArg (fun u : code d ⟶ single e ↦ u.map)
    (collapse_natural (singleOperator a h₀ h₁))
  change (padded (singleOperator a h₀ h₁)).map ≫ collapseMap e =
    collapseMap d ≫ (singleOperator a h₀ h₁).map at h
  rw [← Category.assoc, h]
  simp only [singleOperator, Category.assoc, Iso.inv_hom_id_assoc]

/-- Both original operators commute on the complete padded parameter. -/
theorem parameter_mixed {k l : SimplexCategory} (a : ⦋d⦌ ⟶ ⦋e⦌)
    (h₀ : a.toOrderHom 0 = 0) (h₁ : a.toOrderHom (Fin.last d) = Fin.last e)
    (b : k ⟶ l) {s : Δ ⦋d⦌ ⟶ J.obj k} {t : Δ ⦋e⦌ ⟶ J.obj l}
    (h : s ≫ J.map b = SSet.stdSimplex.map a ≫ t) :
    nativeGraphParameter s ≫ J.map b =
      (padded (singleOperator a h₀ h₁)).map ≫ nativeGraphParameter t := by
  rw [nativeGraphParameter_map, h, parameter_horizontal]

open JTProjectiveOrderedFiberComparison (row)

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev rows (W : Source) :=
  JTRealizationDiagonal.ordinaryCurry.obj (JTReversalInput.ordinaryInput.obj W)

private theorem rowVertex_restrict (W : Source) (a : ⦋d⦌ ⟶ ⦋e⦌) (i : Fin (d + 1)) :
    (rows W).map a.op ≫ rowVertex W ⦋d⦌ i = rowVertex W ⦋e⦌ (a.toOrderHom i) := by
  unfold rowVertex
  change (rows W).map a.op ≫ (rows W).map (SimplexCategory.const ⦋0⦌ ⦋d⦌ i).op =
    (rows W).map (SimplexCategory.const ⦋0⦌ ⦋e⦌ (a.toOrderHom i)).op
  rw [← Functor.map_comp, ← op_comp, SimplexCategory.const_comp]

private theorem graphIndex_restrict {k : SimplexCategory} (a : ⦋d⦌ ⟶ ⦋e⦌)
    (s : Δ ⦋e⦌ ⟶ J.obj k) (i : Fin (d + 1)) :
    graphIndex ⦋d⦌ k (SSet.stdSimplex.map a ≫ s) i =
      graphIndex ⦋e⦌ k s (a.toOrderHom i) := by
  unfold graphIndex
  rw [← Category.assoc, vertex_map]

/-- Horizontal restriction keeps both entire endpoint families and their
specified degenerate faces. -/
def restrictFamilies {W : Source} {k : SimplexCategory} (a : ⦋d⦌ ⟶ ⦋e⦌)
    (h₀ : a.toOrderHom 0 = 0) (h₁ : a.toOrderHom (Fin.last d) = Fin.last e)
    {f : Δ k ⟶ row W ⦋e⦌} {s : Δ ⦋e⦌ ⟶ J.obj k}
    {x y : (row W ⦋0⦌).obj (op ⦋0⦌)} (E : EdgeFamilies W ⦋e⦌ k f s x y) :
    EdgeFamilies W ⦋d⦌ k (f ≫ (rows W).map a.op) (SSet.stdSimplex.map a ≫ s) x y where
  left := E.left
  right := E.right
  left_boundary := by
    rw [Category.assoc, rowVertex_restrict, h₀]
    exact E.left_boundary
  right_boundary := by
    have h : (f ≫ (rows W).map a.op) ≫ rowVertex W ⦋d⦌ (Fin.last ⦋d⦌.len) =
        f ≫ rowVertex W ⦋e⦌ (Fin.last ⦋e⦌.len) := by
      rw [Category.assoc, rowVertex_restrict]
      exact congrArg (fun j ↦ f ≫ rowVertex W ⦋e⦌ j) h₁
    rw [h]
    exact E.right_boundary
  left_degenerate := by
    rw [graphIndex_restrict, h₀]
    exact E.left_degenerate
  right_degenerate := by
    have h : graphIndex ⦋d⦌ k (SSet.stdSimplex.map a ≫ s) (Fin.last ⦋d⦌.len) =
        graphIndex ⦋e⦌ k s (Fin.last ⦋e⦌.len) := by
      rw [graphIndex_restrict]
      exact congrArg (graphIndex ⦋e⦌ k s) h₁
    rw [h]
    exact E.right_degenerate

end

end DaggerModels.PartII.JTMixedGraphHorizontalTraversal
