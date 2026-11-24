import OrdinaryCoherentReplacementComparison
import NativeSubcomplexWeakRestriction

/-!
# Exact preimage recognition for the original coherent comparison

The actual diagonal inclusion is pointwise monic. Mathlib identifies its
domain with its literal range. Once that range is the exact preimage of the
replacement coherent subcomplex, native subcomplex pullbacks and right
properness imply weakness of the same constructed comparison map.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryCoherentReplacementPreimage

open OrdinaryCSSLocalization (Space)
open OrdinaryCoherentReplacementComparison
open OrdinarySegalCoherentArrowImage (coherentArrowSubcomplex)

noncomputable section

/-- The diagonal inclusion retains the same subtype value in each degree. -/
theorem diagonalInclusion_mono (W : Space) : Mono (diagonalInclusion W) := by
  rw [NatTrans.mono_iff_mono_app]
  intro q
  apply (mono_iff_injective _).mpr
  intro a b h
  exact Subtype.ext h

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- Exact degreewise preimage membership suffices for weakness of the actual
comparison; the comparison and both original inclusions are unchanged. -/
theorem coherentComparison_weak_of_preimage (W R : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (i : OrdinarySegalVerticalPrecompletion.precompletion W ⟶ R)
    (hi : WeakEquivalence (i.app (op ⦋1⦌)))
    (hm : ∀ q (x : ((OrdinarySegalVerticalPrecompletion.precompletion W).obj
        (op ⦋1⦌)).obj q),
      x ∈ (SSet.Subcomplex.range (diagonalInclusion W)).obj q ↔
        (i.app (op ⦋1⦌)).app q x ∈ (coherentArrowSubcomplex R).obj q) :
    WeakEquivalence (coherentComparison W R hSegal i) := by
  haveI : Mono (diagonalInclusion W) := diagonalInclusion_mono W
  let A := SSet.Subcomplex.range (diagonalInclusion W)
  let a := SSet.Subcomplex.toRange (diagonalInclusion W)
  let c := coherentComparison W R hSegal i
  let g : A.toSSet ⟶ (coherentArrowSubcomplex R).toSSet := inv a ≫ c
  haveI : WeakEquivalence (i.app (op ⦋1⦌)) := hi
  haveI : Fibration (coherentArrowSubcomplex R).ι :=
    OrdinarySegalCoherentArrowImage.coherentArrow_inclusion_fibration R
  have hg : g ≫ (coherentArrowSubcomplex R).ι = A.ι ≫ i.app (op ⦋1⦌) := by
    apply (cancel_epi a).mp
    dsimp only [g]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rw [coherentComparison_inclusion]
    change diagonalInclusion W ≫ i.app (op ⦋1⦌) = _
    rw [← Category.assoc, SSet.Subcomplex.toRange_ι]
  haveI : WeakEquivalence g :=
    DaggerNativeSubcomplexWeakRestriction.weakEquivalence
      (i.app (op ⦋1⦌)) A (coherentArrowSubcomplex R) g hg hm
  have hc : a ≫ g = c := by
    dsimp only [g]
    rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  change WeakEquivalence c
  rw [← hc]
  infer_instance

#print axioms diagonalInclusion_mono
#print axioms coherentComparison_weak_of_preimage

end

end DaggerModels.PartII.OrdinaryCoherentReplacementPreimage
