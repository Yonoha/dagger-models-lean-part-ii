import DaggerModelsPartII.ConstantVertexAdjunction
import DaggerModelsPartII.SegalLocalizationModels
import DaggerModelsPartII.ActualSegalLocalization
import ActualDaggerRigidificationQuillen

/-!
# Theorem C: the dagger Joyal–Tierney comparison

The main clause fixes the literal constant-vertex adjunction and the original
dagger Joyal and localized injective Segal models at simplicial-set universe
zero. The zigzag records all four Quillen equivalences with their left-adjoint
directions. This file contains statements only.
-/

set_option autoImplicit false

open CategoryTheory DaggerModels

namespace DaggerModels.PartII.TheoremCStatement

open SegalLocalizers ActualIndexProjectiveModel ConstantVertexAdjunction

noncomputable section

/-- The original `δ ⊣ i₀*` is a Quillen equivalence from the dagger Joyal model
to the localized injective complete dagger Segal space model. -/
def mainStatement : Prop :=
  @Adjunction.IsQuillenEquivalence DaggerSSet.{0} ReverseDaggerSpace.{0} _ _
    DaggerOriginalJoyalModel.standardModelCategory.{0} injectiveSegalModel
    delta.{0} vertex.{0} adjunction.{0}

/-- The Part I rigidification is the left adjoint, directed from dagger simplicial
sets to dagger simplicial categories. -/
def partIStatement : Prop :=
  @Adjunction.IsQuillenEquivalence DaggerSSet.{0} DaggerSimplicialCat.{0, 0} _ _
    DaggerActualRigidificationQuillen.modelD.{0}
    DaggerActualRigidificationQuillen.modelG.{0}
    OrdinaryRigidification.DaggerRigidification.daggerRigidification.{0}
    OrdinaryRigidification.DaggerNerve.daggerCoherentNerve.{0}
    DaggerActualRigidificationQuillen.adjunction.{0}

/-- The identity left Quillen functor points from projective to injective
localization on reversal diagrams. -/
def reversalIdentityStatement : Prop :=
  @Adjunction.IsQuillenEquivalence ReverseDaggerSpace.{0} ReverseDaggerSpace.{0} _ _
    projectiveSegalModel injectiveSegalModel
    (𝟭 ReverseDaggerSpace.{0}) (𝟭 ReverseDaggerSpace.{0}) Adjunction.id

/-- The actual change-of-index left adjoint points from reversal diagrams to
diagrams on free dagger simplices. -/
def indexChangeStatement : Prop :=
  @Adjunction.IsQuillenEquivalence ReverseDaggerSpace.{0} ActualSpace _ _
    projectiveSegalModel actualSegalModel
    actualLeftExtension.{0} actualRestriction.{0} actualLeftAdjunction.{0}

/-- The four links in the corollary's zigzag, with each left adjoint typed in
its actual direction. -/
def zigzagStatement : Prop :=
  partIStatement ∧ mainStatement ∧ reversalIdentityStatement ∧ indexChangeStatement

/-- Theorem C, including its dagger Joyal–Tierney equivalence and zigzag. -/
def statement : Prop := zigzagStatement

end

end DaggerModels.PartII.TheoremCStatement
