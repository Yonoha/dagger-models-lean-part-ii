import TheoremCOriginalFourLinksAudit

/-!
# Paper-facing entry point for Part II Theorem C

The original universe-zero four-link statement is retained verbatim.
This file only re-exports its checked proof; it changes no definition or model.
-/

set_option autoImplicit false
set_option warningAsError true

namespace DaggerModelsPartIICompanion

/-- The unchanged original four-link Theorem C of Part II. -/
theorem mainC : DaggerModels.PartII.TheoremCStatement.statement :=
  DaggerModels.PartII.TheoremCOriginalCompletionProof.original_statement

#print axioms mainC

end DaggerModelsPartIICompanion
