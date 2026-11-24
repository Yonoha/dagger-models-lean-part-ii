import DaggerModelsPartII.TheoremCStatement
import DaggerModelsPartII.ActualLocalizedEquivalence
import ProofActualDaggerQuillenEquivalence

/-!
# Previously proved links of the Theorem C zigzag

The original Part I adjunction and the two Theorem B comparisons are reused
with exactly the model structures fixed in the statement. The new
constant–vertex Segal Quillen equivalence is not asserted in this file.
-/

set_option autoImplicit false

namespace DaggerModels.PartII.TheoremCComparisonLinks

/-- The first link is the already proved actual Part I Quillen equivalence. -/
theorem partI : TheoremCStatement.partIStatement :=
  DaggerActualDaggerQuillenEquivalenceProof.quillen_verified.{0}

/-- The identity left adjoint runs from the projective to the injective localization. -/
theorem reversalIdentity : TheoremCStatement.reversalIdentityStatement :=
  SegalLocalizers.segalIdentity_isQuillenEquivalence

/-- The last link is the actual left Kan extension of Theorem B. -/
theorem indexChange : TheoremCStatement.indexChangeStatement :=
  ActualLocalizedEquivalence.actualLeftAdjunction_isQuillenEquivalence

end DaggerModels.PartII.TheoremCComparisonLinks
