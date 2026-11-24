import OrdinaryCoherentDiagonalEndpointWeak
import OrdinaryCoherentReplacementComparison
import OrdinaryPrecompletionReplacementSegal

/-!
# Completeness reduces to the actual coherent comparison

The actual injective rowwise weak replacement is already Segal. The selected
endpoint triangle and the weak coherent-resolution diagonal endpoint make its
completeness equivalent to weakness of the same constructed coherent-arrow
comparison. This is a reduction, not a proof of that remaining weakness.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryPrecompletionCompletenessReduction

open OrdinaryCSSLocalization (Space)
open OrdinaryCoherentReplacementComparison (coherentComparison coherentComparison_endpoint)
open OrdinaryCoherentCompletenessCriterion (endpoint completeness_iff_endpoint_weak)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- Under the original replacement hypotheses, completeness is equivalent to
weakness of the exact coherent comparison with its fixed selected endpoint. -/
theorem completeness_iff_coherentComparison_weak (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) (R : Space) [IsFibrant R]
    (i : OrdinarySegalVerticalPrecompletion.precompletion W ⟶ R)
    (hi : ∀ j : SimplexCategoryᵒᵖ, WeakEquivalence (i.app j)) :
    OrdinaryCSSConditions.completenessCondition R ↔
      WeakEquivalence (coherentComparison W R hSegal i) := by
  have hR := OrdinaryPrecompletionReplacementSegal.replacement_segal W hSegal R i hi
  haveI : WeakEquivalence (OrdinaryCoherentPrecompletionResolution.diagonalEndpoint W) :=
    OrdinaryCoherentDiagonalEndpointWeak.diagonalEndpoint_weak W hSegal
  haveI : WeakEquivalence (i.app (op ⦋0⦌)) := hi _
  have hcomp : WeakEquivalence (coherentComparison W R hSegal i ≫ endpoint R) := by
    rw [coherentComparison_endpoint]
    infer_instance
  refine (completeness_iff_endpoint_weak R hR).trans ?_
  constructor
  · intro h
    haveI : WeakEquivalence (endpoint R) := h
    exact (weakEquivalence_postcomp_iff _ _).mp hcomp
  · intro h
    haveI : WeakEquivalence (coherentComparison W R hSegal i) := h
    exact (weakEquivalence_precomp_iff _ _).mp hcomp

#print axioms completeness_iff_coherentComparison_weak

end

end DaggerModels.PartII.OrdinaryPrecompletionCompletenessReduction
