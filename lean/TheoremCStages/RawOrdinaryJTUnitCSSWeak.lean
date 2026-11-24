import OrdinaryJTCSSQuillenEquivalence
import RawOrdinaryJTQuillenTranspose
import OrdinaryJoyalFibrancy

/-!
# The literal raw ordinary JT transpose is CSS weak

The actual realization-side map `leftComparison W` is original Joyal weak,
and its curried adjoint transpose is exactly the original `gRawTilde W`.
The ordinary JT Quillen equivalence transfers this weakness to the exact
ordinary CSS model. Every CSS object is cofibrant, and the actual raw
target is a Joyal-fibrant quasicategory. No locality premise on `W` is
needed for this result; no ordered-fiber conclusion is asserted here.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite HomotopicalAlgebra

namespace DaggerModels.PartII.RawOrdinaryJTUnitCSSWeak

open OrdinaryCSSLocalization (Space)
open OrdinaryJTProjectiveQuillen (joyalModel)
open OrdinaryJTCurriedAdjunction (left right adjunction)
open RawOrdinaryJTQuillenTranspose (input leftComparison)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

private local instance : ModelCategory Space := OrdinaryCSSLocalization.model
private local instance : CategoryWithFibrations Space :=
  OrdinaryCSSLocalization.model.categoryWithFibrations
private local instance : CategoryWithCofibrations Space :=
  OrdinaryCSSLocalization.model.categoryWithCofibrations
private local instance : CategoryWithWeakEquivalences Space :=
  OrdinaryCSSLocalization.model.categoryWithWeakEquivalences
private local instance : ModelCategory SSet.{0} := joyalModel
private local instance : CategoryWithFibrations SSet.{0} :=
  joyalModel.categoryWithFibrations
private local instance : CategoryWithCofibrations SSet.{0} :=
  joyalModel.categoryWithCofibrations
private local instance : CategoryWithWeakEquivalences SSet.{0} :=
  joyalModel.categoryWithWeakEquivalences

private theorem input_cofibrant (W : Source) : IsCofibrant (input W) := by
  rw [isCofibrant_iff, cofibration_iff]
  change OrdinaryCSSLocalization.model.categoryWithCofibrations.cofibrations
    (initial.to (input W))
  rw [OrdinaryCSSLocalization.exactClasses.1]
  letI : ModelCategory Space :=
    InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ
  letI : CategoryWithCofibrations Space :=
    (InjectiveKanDiagram.modelCategory
      SimplexCategoryᵒᵖ).categoryWithCofibrations
  exact (cofibration_iff _).mp
    (InjectiveKanDiagram.model_isCofibrant SimplexCategoryᵒᵖ (input W))

/-- The curry of the exact original raw transpose is weak in the original
ordinary CSS localization, for every original reversal-space input. -/
theorem rawTranspose_cssWeak (W : Source) :
    OrdinaryCSSLocalization.model.categoryWithWeakEquivalences.weakEquivalences
      (JTRealizationDiagonal.ordinaryCurry.map
        (JTRawOrdinaryAdjoint.gRawTilde W)) := by
  letI : IsCofibrant (input W) := input_cofibrant W
  letI : IsFibrant (JTRawFreeInnerComparison.rawTarget W).toSSet :=
    (OrdinaryJoyalFibrancy.isFibrant_iff_quasicategory _).mpr
      (RawOrdinaryJTRightNerve.rawTarget_quasicategory W)
  letI : adjunction.IsQuillenEquivalence :=
    OrdinaryJTCSSQuillenEquivalence.isQuillenEquivalence
  have hleft : WeakEquivalence (leftComparison W) :=
    (weakEquivalence_iff _).mpr
      (RawOrdinaryJTQuillenTranspose.leftComparison_weak W)
  have hright : WeakEquivalence
      ((adjunction.homEquiv (input W)
        (JTRawFreeInnerComparison.rawTarget W).toSSet)
          (leftComparison W)) :=
    (adjunction.weakEquivalence_homEquiv_iff (leftComparison W)).mpr hleft
  change weakEquivalences Space
    (JTRealizationDiagonal.ordinaryCurry.map
      (JTRawOrdinaryAdjoint.gRawTilde W))
  rw [← RawOrdinaryJTQuillenTranspose.transpose_eq W]
  exact (weakEquivalence_iff _).mp hright

#print axioms rawTranspose_cssWeak

end

end DaggerModels.PartII.RawOrdinaryJTUnitCSSWeak
