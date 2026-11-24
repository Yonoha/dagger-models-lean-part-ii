import OrdinaryFirstRowAdjunction
import OrdinaryCSSHorizontalWeak
import OrdinaryCSSConditions
import OrdinarySpaceReedyInjective
import OrdinaryReedyVerticalConstancy

/-!
# The actual first-row counit is a CSS weak equivalence on fibrant targets

Each original horizontal row of the actual counit is the vertical collapse
operator of its target. Reedy--Kan fibrancy gives its original Joyal
weakness, and the horizontal-to-CSS theorem applies without imposing
fibrancy on the discrete source.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryFirstRowCounitWeak

open OrdinaryCSSLocalization (Space)

noncomputable section

private local instance : ModelCategory Space := OrdinarySpaceReedyInjective.reedyModel

/-- The exact counit, with its original horizontally discrete source,
is a CSS weak equivalence for every CSS-fibrant ordinary simplicial space. -/
theorem counit_weak (W : Space)
    (hW : @IsFibrant Space _ OrdinaryCSSLocalization.model.categoryWithFibrations _ W) :
    OrdinaryCSSLocalization.model.categoryWithWeakEquivalences.weakEquivalences
      (OrdinaryFirstRowAdjunction.adjunction.counit.app W) := by
  have hbase := ((OrdinaryCSSConditions.isFibrant_iff W).mp hW).1
  have hR : IsFibrant W := by
    rw [isFibrant_iff, fibration_iff]
    change OrdinarySpaceReedyInjective.reedyModel.categoryWithFibrations.fibrations
      (terminal.from W)
    rw [OrdinarySpaceReedyInjective.fibrations_eq]
    letI : ModelCategory Space := OrdinarySpaceReedyInjective.injectiveModel
    exact (fibration_iff _).mp hbase
  haveI := hR
  apply OrdinaryCSSHorizontalWeak.weak_of_rows
  intro k
  induction k using SimplexCategory.rec with
  | h n =>
    let c := SimplexCategory.isTerminalZero.from ⦋n⦌
    have hrow :
        ((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type 0)).map
          (OrdinaryFirstRowAdjunction.adjunction.counit.app W)).app (op ⦋n⦌) =
          W.flip.map c.op := by
      apply NatTrans.ext
      funext q
      exact OrdinaryFirstRowAdjunction.counit_app_app W q.unop ⦋n⦌
    rw [hrow]
    exact OrdinaryReedyVerticalConstancy.collapse_weak W n

#print axioms counit_weak

end
end DaggerModels.PartII.OrdinaryFirstRowCounitWeak
