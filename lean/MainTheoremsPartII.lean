import DaggerModelsPartII.ProofTheoremA
import DaggerModelsPartII.ProofTheoremB
import MainTheoremCPartII

/-!
# Paper-facing entry points for the three main theorems of Part II

These aliases retain the existing statements. Theorem A has its original
universe parameter; the assembled Theorems B and C have value universe zero.
Theorem B includes the literal simplicial enrichment data, not only its core.
-/

set_option autoImplicit false
set_option warningAsError true

universe u

namespace DaggerModelsPartIICompanion

/-- The original resolution-model Theorem A, with its universe parameter. -/
theorem mainA : DaggerModels.PartII.TheoremAStatement.statement.{u} :=
  DaggerModels.PartII.theoremA

/-- The full original Theorem B, including literal simplicial structure. -/
theorem mainB : DaggerModels.PartII.FullTheoremBStatement.fullStatement :=
  DaggerModels.PartII.theoremB

#print axioms mainA
#print axioms mainB
#print axioms mainC

end DaggerModelsPartIICompanion
