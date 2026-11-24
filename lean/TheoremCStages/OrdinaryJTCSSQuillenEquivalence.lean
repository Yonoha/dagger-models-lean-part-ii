import OrdinaryFirstRowQuillenEquivalence
import OrdinaryJTDiscreteRealizationIdentity
import OrdinaryJTCSSQuillen
import QuillenEquivalenceRightCancellation
import AdjunctionLeftIdentityQuillenEquivalence

/-!
# Quillen equivalence of the actual ordinary Joyal--Tierney adjunction

The actual discrete/first-row pair is a Quillen equivalence. Its composite
with the actual JT pair has left adjoint naturally isomorphic to identity.
Right cancellation therefore proves Quillen equivalence for the original
curried JT realization and native nerve, using the fixed CSS and Joyal models.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

namespace DaggerModels.PartII.OrdinaryJTCSSQuillenEquivalence

open OrdinaryCSSLocalization (Space discrete)
open OrdinaryJTProjectiveQuillen (joyalModel)
open OrdinaryJTCurriedAdjunction (left right adjunction)

noncomputable section

private local instance : ModelCategory SSet.{0} := joyalModel
private local instance : CategoryWithFibrations SSet.{0} := joyalModel.categoryWithFibrations
private local instance : CategoryWithCofibrations SSet.{0} := joyalModel.categoryWithCofibrations
private local instance : CategoryWithWeakEquivalences SSet.{0} :=
  joyalModel.categoryWithWeakEquivalences
private local instance : ModelCategory Space := OrdinaryCSSLocalization.model
private local instance : CategoryWithFibrations Space :=
  OrdinaryCSSLocalization.model.categoryWithFibrations
private local instance : CategoryWithCofibrations Space :=
  OrdinaryCSSLocalization.model.categoryWithCofibrations
private local instance : CategoryWithWeakEquivalences Space :=
  OrdinaryCSSLocalization.model.categoryWithWeakEquivalences

private theorem joyal_isCofibrant (X : SSet.{0}) : IsCofibrant X := by
  rw [isCofibrant_iff, cofibration_iff]
  change joyalModel.categoryWithCofibrations.cofibrations (initial.to X)
  rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelCof,
    DaggerNativeFullWeakSmithGenerators.boundary_cof]
  exact monomorphisms.infer_property _

private theorem css_isCofibrant (X : Space) : IsCofibrant X := by
  rw [isCofibrant_iff, cofibration_iff]
  change OrdinaryCSSLocalization.model.categoryWithCofibrations.cofibrations (initial.to X)
  rw [OrdinaryCSSLocalization.exactClasses.1]
  letI : ModelCategory Space := InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ
  letI : CategoryWithCofibrations Space :=
    (InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ).categoryWithCofibrations
  exact (cofibration_iff _).mp (InjectiveKanDiagram.model_isCofibrant SimplexCategoryᵒᵖ X)

private theorem composite_isQuillenAdjunction :
    (OrdinaryFirstRowAdjunction.adjunction.comp adjunction).IsQuillenAdjunction := by
  let a := OrdinaryFirstRowAdjunction.adjunction
  letI : a.IsQuillenAdjunction := OrdinaryFirstRowQuillen.isQuillenAdjunction
  letI : adjunction.IsQuillenAdjunction := OrdinaryJTCSSQuillen.isQuillenAdjunction
  letI : discrete.PreservesCofibrations :=
    Adjunction.IsQuillenAdjunction.preservesCofibrations a
  letI : left.PreservesCofibrations :=
    Adjunction.IsQuillenAdjunction.preservesCofibrations adjunction
  letI : OrdinaryFirstRowAdjunction.firstRow.PreservesFibrations :=
    Adjunction.IsQuillenAdjunction.preservesFibrations a
  letI : right.PreservesFibrations :=
    Adjunction.IsQuillenAdjunction.preservesFibrations adjunction
  letI : (discrete ⋙ left).PreservesCofibrations := ⟨by
    intro X Y f hf
    change Cofibration (left.map (discrete.map f))
    infer_instance⟩
  letI : (right ⋙ OrdinaryFirstRowAdjunction.firstRow).PreservesFibrations := ⟨by
    intro X Y f hf
    change Fibration (OrdinaryFirstRowAdjunction.firstRow.map (right.map f))
    infer_instance⟩
  exact ⟨⟩

/-- The original ordinary JT realization/native-nerve adjunction is a
Quillen equivalence for the exact ordinary CSS and original Joyal models. -/
theorem isQuillenEquivalence :
    @Adjunction.IsQuillenEquivalence Space SSet.{0} _ _ OrdinaryCSSLocalization.model
      joyalModel left right adjunction := by
  let a := OrdinaryFirstRowAdjunction.adjunction
  have hComp : (a.comp adjunction).IsQuillenEquivalence := by
    letI : (a.comp adjunction).IsQuillenAdjunction := composite_isQuillenAdjunction
    exact AdjunctionLeftIdentityQuillenEquivalence.of_left_identity (a.comp adjunction)
      OrdinaryJTDiscreteRealizationIdentity.discreteRealizationIdentityIso
  exact QuillenEquivalenceRightCancellation.isQuillenEquivalence discrete
    OrdinaryFirstRowAdjunction.firstRow left right a adjunction
    OrdinaryFirstRowQuillenEquivalence.isQuillenEquivalence
    OrdinaryJTCSSQuillen.isQuillenAdjunction hComp joyal_isCofibrant css_isCofibrant

#print axioms composite_isQuillenAdjunction
#print axioms isQuillenEquivalence

end
end DaggerModels.PartII.OrdinaryJTCSSQuillenEquivalence
