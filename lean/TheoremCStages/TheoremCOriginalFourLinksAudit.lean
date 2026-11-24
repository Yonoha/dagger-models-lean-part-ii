import TheoremCOriginalCompletionProof

/-!
# Literal target audit for the four original links of Theorem C

Each target is written using the original model and adjunction expressions,
as in the protected current TheoremCStatement source. This is a kernel target
audit, not a trusted Challenge replacement or a claim of a Comparator run.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory DaggerModels

namespace DaggerModels.PartII.TheoremCOriginalFourLinksAudit

open SegalLocalizers ActualIndexProjectiveModel ConstantVertexAdjunction

noncomputable section

/-- The original Part I rigidification, with its original left-adjoint direction. -/
theorem partI :
    @Adjunction.IsQuillenEquivalence DaggerSSet.{0} DaggerSimplicialCat.{0, 0} _ _
      DaggerActualRigidificationQuillen.modelD.{0}
      DaggerActualRigidificationQuillen.modelG.{0}
      OrdinaryRigidification.DaggerRigidification.daggerRigidification.{0}
      OrdinaryRigidification.DaggerNerve.daggerCoherentNerve.{0}
      DaggerActualRigidificationQuillen.adjunction.{0} :=
  TheoremCOriginalCompletionProof.original_statement.1

/-- The literal constant-vertex adjunction for the original two models. -/
theorem constantVertex :
    @Adjunction.IsQuillenEquivalence DaggerSSet.{0} ReverseDaggerSpace.{0} _ _
      DaggerOriginalJoyalModel.standardModelCategory.{0} injectiveSegalModel
      delta.{0} vertex.{0} adjunction.{0} :=
  TheoremCOriginalCompletionProof.original_statement.2.1

/-- The original projective-to-injective identity left adjoint. -/
theorem reversalIdentity :
    @Adjunction.IsQuillenEquivalence ReverseDaggerSpace.{0} ReverseDaggerSpace.{0} _ _
      projectiveSegalModel injectiveSegalModel
      (𝟭 ReverseDaggerSpace.{0}) (𝟭 ReverseDaggerSpace.{0}) Adjunction.id :=
  TheoremCOriginalCompletionProof.original_statement.2.2.1

/-- The original actual left extension and restriction along the actual index change. -/
theorem indexChange :
    @Adjunction.IsQuillenEquivalence ReverseDaggerSpace.{0} ActualSpace _ _
      projectiveSegalModel actualSegalModel
      actualLeftExtension.{0} actualRestriction.{0} actualLeftAdjunction.{0} :=
  TheoremCOriginalCompletionProof.original_statement.2.2.2

#print axioms partI
#print axioms constantVertex
#print axioms reversalIdentity
#print axioms indexChange

end

end DaggerModels.PartII.TheoremCOriginalFourLinksAudit
