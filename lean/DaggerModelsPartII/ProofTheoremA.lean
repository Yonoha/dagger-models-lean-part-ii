import DaggerModelsPartII.TheoremAStatement
import DaggerModelsPartII.ResolutionModel

/-! The kernel-checked proof of the separately stated Part II Theorem A. -/

set_option autoImplicit false

universe u

namespace DaggerModels.PartII

/-- Theorem A of Models for dagger categories II. -/
theorem theoremA : TheoremAStatement.statement.{u} :=
  ⟨resolutionLocalizedModelCategory, resolutionLocalized_cofibrations,
    resolutionLocalized_weakEquivalences, fun sq hw hc ↦ resolutionLocalized_leftProper sq hw hc,
    resolutionLocalized_combinatorial, resolutionLocalized_isFibrant_iff_local,
    resolutionLocalized_isFibrant_iff, resolutionLocalized_constantEvaluation⟩

end DaggerModels.PartII
