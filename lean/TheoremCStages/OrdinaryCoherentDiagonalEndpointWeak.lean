import OrdinaryWalkingPrecompletionExchangeEndpoint
import OrdinaryPrecompletionConstantSectionWeak

/-!
# Weakness of the actual coherent-resolution diagonal endpoint

The walking exchange and its original selected endpoint identify the complete
composite with corrected precompletion of the actual parameter evaluation.
The literal walking contraction and diagonal coherent evaluation then imply
weakness of the endpoint of the coherent-resolution diagonal. Comparison with
the coherent image of an injectively fibrant replacement remains separate.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerNativeBisimplicialDiagonal (diagonalFunctor)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryCoherentDiagonalEndpointWeak

open OrdinaryCSSLocalization (Space)
open OrdinaryCoherentPrecompletionResolution
open OrdinaryWalkingPrecompletionExchangeEndpoint

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- The original selected endpoint of the coherent-resolution diagonal is weak. -/
theorem diagonalEndpoint_weak (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) :
    WeakEquivalence (diagonalEndpoint W) := by
  have : WeakEquivalence (diagonalFunctor.map (evaluationResolution W)) :=
    evaluationResolution_diagonal_weak W hSegal
  have : WeakEquivalence
      ((OrdinarySegalVerticalPrecompletionNaturality.precompletionMap
        (selectedEvaluation W)).app (op ⦋0⦌)) :=
    OrdinaryPrecompletionConstantSectionWeak.evaluation_row_weak ⦋1⦌ 0 W ⦋0⦌
  have h : WeakEquivalence
      (diagonalFunctor.map (evaluationResolution W) ≫ diagonalEndpoint W) := by
    rw [diagonal_endpoint_square]
    infer_instance
  exact (weakEquivalence_precomp_iff _ _).mp h

#print axioms diagonalEndpoint_weak

end

end DaggerModels.PartII.OrdinaryCoherentDiagonalEndpointWeak
