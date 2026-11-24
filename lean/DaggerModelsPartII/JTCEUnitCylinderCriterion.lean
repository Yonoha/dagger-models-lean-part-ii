import DaggerModelsPartII.JTCylinderMappingWeak
import DaggerModelsPartII.JTConeLatchingMono

/-!
# Only the literal cylinder augmentation remains for the chosen CE unit

The original cone under-Reedy condition is now proved. The exact Hom
span and chosen cone unit therefore reduce the actual CE unit weakness
to the sole remaining original Joyal cylinder augmentation input.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.JTCEUnitCylinderCriterion

open JTStrictificationCoefficients JTChosenCEUnitBoundary

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

/-- The SAME chosen ordinary unit induces a Kan weak map on actual CE
Hom if the specified literal cylinder augmentation is original Joyal weak.
The original cone Reedy condition is proved, not an additional input. -/
theorem etaCE_GW_of_cylinder_augmentation
    (hCyl : ∀ k : SimplexCategory,
      DaggerNativeJoyalMappingTest.weakCategoricalEquivalences
        (JTCylinderFrame.augmentation.app k))
    (W : Source) (x y : (chosenT W).toSSet.obj (op ⦋0⦌)) :
    DaggerSSetGluing.GW
      (JTCEPlainMappingTarget.plainCEHomMap (etaUnder W x y)) :=
  JTCylinderMappingWeak.etaCE_GW_of_frame_inputs hCyl
    JTConeLatchingMono.coneUnder_op_isFibrant W x y

end

end DaggerModels.PartII.JTCEUnitCylinderCriterion
