import OrdinaryCoherentZeroProjection
import OrdinaryCoherentWeakInvariance
import OrdinaryAllVertexReplacementSegalReduction

/-!
# Coherent-arrow reflection from the actual weak relative comparison

Pulling the target back to the same source zero row gives an injectively
fibrant target. The already weak relative comparison reflects coherent arrows
by mapping-space invariance; the strict zero-coskeleton projection reflects
them by its walking-extension pullback. Their exact original composite is
therefore coherent-reflecting, including the actual precompletion unit.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryCoherentRelativeReflection

open OrdinaryCSSLocalization (Space)
open OrdinaryZeroCoskeleton (targetOverZero relativeComparison vertices coskeleton)
open OrdinarySegalCoherentArrowImage (coherentArrowSubcomplex)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- An actual weak comparison over the original source zero row makes the
same whole target map reflect coherent membership in every degree. -/
theorem relative_weak_reflects {W Z : Space} [IsFibrant W] [IsFibrant Z]
    (f : W ⟶ Z) [WeakEquivalence (relativeComparison f)]
    (q : SimplexCategoryᵒᵖ) (e : (W.obj (op ⦋1⦌)).obj q) :
    e ∈ (coherentArrowSubcomplex W).obj q ↔
      (f.app (op ⦋1⦌)).app q e ∈ (coherentArrowSubcomplex Z).obj q := by
  haveI : IsFibrant (W.obj (op ⦋0⦌)) :=
    OrdinarySegalWalkingEvaluation.row_isFibrant W 0
  haveI : IsFibrant (targetOverZero f) :=
    OrdinaryZeroCoskeleton.targetOverZero_fibrant f
  let p := pullback.fst (vertices Z) (coskeleton.map (f.app (op ⦋0⦌)))
  have h : relativeComparison f ≫ p = f := pullback.lift_fst _ _ _
  calc
    e ∈ (coherentArrowSubcomplex W).obj q ↔
        ((relativeComparison f).app (op ⦋1⦌)).app q e ∈
          (coherentArrowSubcomplex (targetOverZero f)).obj q :=
      OrdinaryCoherentWeakInvariance.coherent_membership_iff (relativeComparison f) q e
    _ ↔ (p.app (op ⦋1⦌)).app q
        (((relativeComparison f).app (op ⦋1⦌)).app q e) ∈
          (coherentArrowSubcomplex Z).obj q :=
      OrdinaryCoherentZeroProjection.projection_reflects_coherent f q _
    _ ↔ (f.app (op ⦋1⦌)).app q e ∈ (coherentArrowSubcomplex Z).obj q := by
      have he := congrFun (NatTrans.congr_app (NatTrans.congr_app h (op ⦋1⦌)) q) e
      exact Iff.of_eq (congrArg (fun x ↦ x ∈ (coherentArrowSubcomplex Z).obj q) he)

/-- The original corrected unit followed by the specified weak fibrant
replacement reflects coherent arrows without a completeness assumption. -/
theorem replacement_reflects (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) (R : Space) [IsFibrant R]
    (i : OrdinarySegalVerticalPrecompletion.precompletion W ⟶ R)
    (hi : ∀ j : SimplexCategoryᵒᵖ, WeakEquivalence (i.app j))
    (q : SimplexCategoryᵒᵖ) (e : (W.obj (op ⦋1⦌)).obj q) :
    e ∈ (coherentArrowSubcomplex W).obj q ↔
      ((OrdinarySegalVerticalPrecompletion.unit W ≫ i).app (op ⦋1⦌)).app q e ∈
        (coherentArrowSubcomplex R).obj q := by
  haveI : WeakEquivalence (relativeComparison
      (OrdinarySegalVerticalPrecompletion.unit W ≫ i)) :=
    OrdinaryAllVertexReplacementSegalReduction.replacement_relativeComparison_weak
      W hSegal R i hi
  exact relative_weak_reflects (OrdinarySegalVerticalPrecompletion.unit W ≫ i) q e

#print axioms relative_weak_reflects
#print axioms replacement_reflects

end

end DaggerModels.PartII.OrdinaryCoherentRelativeReflection
