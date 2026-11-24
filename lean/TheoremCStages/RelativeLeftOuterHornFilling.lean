import RelativeLeftOuterHornGeometry
import RelativeHornReversedExtension

/-!
# Horn-level first/last edge calibration for relative outer fillers

The ambient edge comparison is lifted to an equality inside the actual
reversed horn by cancelling its monic inclusion. This keeps the selected
first edge of the original left horn identical to the selected last edge
of the reversed right horn, before any invertibility premise is used.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial
open DaggerOriginalHornReversal DaggerOriginalHornFillingReversal
open DaggerOriginalStandardSimplexReversal
open DaggerModels.PartII.RelativeLeftOuterHornGeometry

universe u

namespace DaggerModels.PartII.RelativeLeftOuterHornFilling

noncomputable section

private theorem reversed_zero_eq_last (k : ℕ) :
    (0 : Fin (k + 3)).rev = Fin.last (k + 2) := by
  apply Fin.ext
  simp only [Fin.val_rev, Fin.val_zero, Fin.val_last]
  omega

/-- The old right-horn last edge, with only its index rewritten as the
reverse of the left-horn omitted vertex. -/
def rightEdgeAtReversedIndex (k : ℕ) :
    (Δ[1] : SSet.{u}) ⟶
      (Λ[k + 2, (0 : Fin (k + 3)).rev] : SSet.{u}) := by
  rw [reversed_zero_eq_last k]
  exact DaggerOriginalRightOuterHornInclusions.rightOuterLastEdgeInclusion k

private theorem rightEdgeAtReversedIndex_comp (k : ℕ) :
    rightEdgeAtReversedIndex.{u} k ≫
        (Λ[k + 2, (0 : Fin (k + 3)).rev] :
          (Δ[k + 2] : SSet.{u}).Subcomplex).ι =
      SSet.stdSimplex.map
        (AugmentedSimplexCategory.inr' ⦋k⦌ ⦋1⦌) := by
  simpa only [rightEdgeAtReversedIndex, reversed_zero_eq_last] using
    DaggerOriginalRightOuterHornInclusions.rightOuterLastEdgeInclusion_comp.{u} k

/-- The selected right-horn last edge is exactly the reverse of the
selected left-horn first edge as a map into the opposite horn. -/
theorem reversed_edge_horn (k : ℕ) :
    rightEdgeAtReversedIndex.{u} k ≫
        hornReversalInv (k + 2) (0 : Fin (k + 3)) =
      standardSimplexReversalInv 1 ≫
        SSet.opFunctor.map (firstEdgeInclusion.{u} k) := by
  haveI : Mono (SSet.opFunctor.map
      (Λ[k + 2, (0 : Fin (k + 3))] :
        (Δ[k + 2] : SSet.{u}).Subcomplex).ι) :=
    DaggerOriginalSimplicialSubcomplexOpposite.mono_op_inclusion _
  apply (cancel_mono (SSet.opFunctor.map
    (Λ[k + 2, (0 : Fin (k + 3))] :
      (Δ[k + 2] : SSet.{u}).Subcomplex).ι)).mp
  calc
    (rightEdgeAtReversedIndex.{u} k ≫
        hornReversalInv (k + 2) (0 : Fin (k + 3))) ≫
          SSet.opFunctor.map Λ[k + 2, (0 : Fin (k + 3))].ι =
      (rightEdgeAtReversedIndex.{u} k ≫
        Λ[k + 2, (0 : Fin (k + 3)).rev].ι) ≫
          standardSimplexReversalInv (k + 2) := by
            rw [Category.assoc, hornReversalInv_comp_ι, ← Category.assoc]
    _ = SSet.stdSimplex.map
          (AugmentedSimplexCategory.inr' ⦋k⦌ ⦋1⦌) ≫
            standardSimplexReversalInv (k + 2) := by
          rw [rightEdgeAtReversedIndex_comp]
    _ = standardSimplexReversalInv 1 ≫
          SSet.opFunctor.map
            (firstEdgeInclusion.{u} k ≫ Λ[k + 2, (0 : Fin (k + 3))].ι) := by
          simpa only [
            DaggerOriginalRightOuterHornInclusions.rightOuterLastEdgeInclusion_comp]
            using reversed_edge_ambient.{u} k
    _ = (standardSimplexReversalInv 1 ≫
          SSet.opFunctor.map (firstEdgeInclusion.{u} k)) ≫
            SSet.opFunctor.map Λ[k + 2, (0 : Fin (k + 3))].ι := by
          simp only [Functor.map_comp, Category.assoc]

/-- The reversed last-edge restriction of the exact horn map is the
opposite of its original first-edge restriction. -/
theorem reversed_edge_image {X : SSet.{u}} (k : ℕ)
    (φ : (Λ[k + 2, (0 : Fin (k + 3))] : SSet.{u}) ⟶ X) :
    rightEdgeAtReversedIndex.{u} k ≫
        reverseHornMap (k + 2) (0 : Fin (k + 3)) φ =
      standardSimplexReversalInv 1 ≫
        SSet.opFunctor.map (firstEdgeInclusion.{u} k ≫ φ) := by
  dsimp only [reverseHornMap]
  rw [← Category.assoc, reversed_edge_horn, Category.assoc,
    ← Functor.map_comp]

#print axioms reversed_edge_horn
#print axioms reversed_edge_image

end

end DaggerModels.PartII.RelativeLeftOuterHornFilling
