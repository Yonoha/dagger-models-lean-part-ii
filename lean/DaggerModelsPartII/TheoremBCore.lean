import DaggerModelsPartII.TheoremBStatement
import DaggerModelsPartII.ActualLocalizedEquivalence

/-!
# The model-theoretic clauses of Theorem B

The separate statement contains left properness, combinatoriality, the literal
pushout-product axiom, the three fibrancy descriptions, and the actual
change-of-index Quillen equivalence. This proof does not claim to package
simplicial enrichment and cotensors, which require separate structural data.
-/

set_option autoImplicit false

namespace DaggerModels.PartII

open SegalLocalizers ActualIndexProjectiveModel

/-- All seven clauses of the existing statement, with its explicit SM7 scope. -/
theorem theoremB_core : TheoremBStatement.statement := by
  refine ⟨?_, injectiveSegalModel_combinatorial, ?_, injectiveSegalModel_isFibrant_iff,
    projectiveSegalModel_isFibrant_iff, actualSegalModel_isFibrant_iff,
    ActualLocalizedEquivalence.actualLeftAdjunction_isQuillenEquivalence⟩
  · intro A B D P i k l r sq hi hk
    exact injectiveSegalModel_leftProper sq hi hk
  · refine ⟨fun A ↦ ⟨diagramTensorMappingAdjunction A⟩, ?_⟩
    intro A B i K L j hi hj sq
    exact injectiveSegalModel_pushoutProduct_sm7 i j hi hj sq

end DaggerModels.PartII
