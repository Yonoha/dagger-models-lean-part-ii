import OrdinarySegalCoherentEvaluationTrivialFibration
import OrdinarySegalRelativeWalkingAudit

/-!
# Coherent evaluation at the original input and its exact strict fibers

The proved Kan trivial fibration applies to the original raw JT ordinary
input using only its checked Kan-injective fibrancy and ordinary Segal
condition. Its pullback over any literal point is again a Kan trivial
fibration to the actual zero-simplex, making the contractibility statement
about the individual strict fibers explicit.

This does not identify the coherent-arrow image with an independently
defined Segal homotopy-category equivalence space, prove the completion
comparison, or discharge the original raw ordered-unit weakness.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalCoherentEvaluationAudit

open OrdinaryCSSLocalization (Space)
open OrdinarySegalCoherentArrowImage
open OrdinarySegalCoherentEvaluationTrivialFibration

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- Each actual strict coherent-evaluation fiber maps to the original
point by a Kan trivial fibration. -/
theorem coherentFiber_projection_trivialFibration (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (b : (coherentArrowSubcomplex W : SSet.{0}).obj (op ⦋0⦌)) :
    trivialFibrations SSet.{0}
      (pullback.snd (coherentEvaluation W) (SSet.yonedaEquiv.symm b)) := by
  have hq := (mem_trivialFibrations_iff (coherentEvaluation W)).mp
    (coherentEvaluation_trivialFibration W hSegal)
  have : Fibration (coherentEvaluation W) := hq.1
  have : WeakEquivalence (coherentEvaluation W) := hq.2
  apply (mem_trivialFibrations_iff _).mpr
  exact ⟨inferInstance,
    SSet.modelCategoryQuillen.weakEquivalence_of_fibration_of_isPullback
      (IsPullback.of_hasPullback (coherentEvaluation W) (SSet.yonedaEquiv.symm b))⟩

/-- The original reverse-dagger Segal input satisfies the whole coherent
evaluation theorem without an ordinary completeness hypothesis. -/
theorem originalInput_coherentEvaluation_trivialFibration
    (W : SegalLocalizers.ReverseDaggerSpace.{0})
    (hW : letI : ModelCategory SegalLocalizers.ReverseDaggerSpace.{0} :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hSegal : SegalLocalizers.segalCondition W) :
    trivialFibrations SSet.{0}
      (coherentEvaluation (RawOrdinaryJTQuillenTranspose.input W)) := by
  have : IsFibrant (RawOrdinaryJTQuillenTranspose.input W) :=
    OrdinaryJTOrdinaryInputReedy.ordinaryInput_injectiveFibrant W hW
  exact coherentEvaluation_trivialFibration (RawOrdinaryJTQuillenTranspose.input W)
    (OrdinaryJTOrdinaryInputSegal.ordinaryInput_segalCondition W hSegal)

#print axioms coherentFiber_projection_trivialFibration
#print axioms originalInput_coherentEvaluation_trivialFibration
#print axioms coherentEvaluation_boundary_lift
#print axioms coherentEvaluation_trivialFibration
#print axioms OrdinaryWalkingRelativeUnitExtension.edge_extension_over
#print axioms OrdinaryWalkingAlternatingPushout.stage_attachment_horn_isPushout
#print axioms OrdinarySegalRestrictionTranspose.simplexUnit_transpose
#print axioms RawOrdinaryJTUnitCSSWeak.rawTranspose_cssWeak
#print axioms JTTheoremCFromOriginalRawOrderedUnit.statement_of_originalRawOrderedUnit

end

end DaggerModels.PartII.OrdinarySegalCoherentEvaluationAudit
