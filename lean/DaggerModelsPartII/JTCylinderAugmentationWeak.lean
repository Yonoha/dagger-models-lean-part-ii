import DaggerModelsPartII.JTCylinderOverlapQuotient
import DaggerModelsPartII.JTCylinderCellRestriction
import DaggerModelsPartII.FiniteOrdinalShellingWeak
import DaggerModelsPartII.JTCEUnitCylinderCriterion

/-!
# Original Joyal weakness of the actual cylinder augmentation

The actual quotient cell cover, adjacent intersection and smaller block
quotient are applied to restrictions of the SAME interval augmentation.
The exact finite shelling theorem includes the one-cell case without an
empty-source weak premise. The chosen CE unit then has no remaining
geometric frame input.
-/

set_option autoImplicit false

open CategoryTheory Simplicial Opposite DaggerModels
open DaggerNativeJoyalMappingTest

namespace DaggerModels.PartII.JTCylinderAugmentationWeak

open JTCylinderQuotientImages JTCylinderQuotientIntersections
open JTStrictificationCoefficients JTChosenCEUnitBoundary

noncomputable section

/-- The SAME interval augmentation is weak on the overlap with every
previous quotient cell union. -/
theorem overlap_previous_augmentation_weak (k : ℕ) (t : Fin (k + 1))
    (ht : 0 < t.val) :
    weakCategoricalEquivalences
      ((quotientImage k t ⊓ previousQuotient k t).ι ≫
        JTCylinderFrame.augmentation.app ⦋k⦌) := by
  rw [quotientImage_adjacent k t ht]
  cases k with
  | zero =>
    have hbound := t.isLt
    omega
  | succ n =>
    let s : Fin (n + 1) := ⟨t.val - 1, by
      have hbound := t.isLt
      omega⟩
    have hs : Fin.succ s = t := by
      apply Fin.ext
      dsimp [s]
      omega
    have hp : Fin.castSucc s = (⟨t.val - 1, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    have h := JTCylinderOverlapQuotient.adjacent_augmentation_weak n s
    rw [hs, hp] at h
    exact h

/-- Every component of the literal standard reduced-cylinder augmentation
is weak in the ORIGINAL ordinary Joyal class. -/
theorem augmentation_nat_weak (k : ℕ) :
    weakCategoricalEquivalences (JTCylinderFrame.augmentation.app ⦋k⦌) := by
  apply FiniteOrdinalShellingWeak.weak_of_cover
    (p := JTCylinderFrame.augmentation.app ⦋k⦌)
    (quotientImage k) (quotient_cover k)
  · exact JTCylinderCellRestriction.quotientImage_augmentation_weak k
  · intro t ht
    change weakCategoricalEquivalences
      ((quotientImage k t ⊓ previousQuotient k t).ι ≫
        JTCylinderFrame.augmentation.app ⦋k⦌)
    exact overlap_previous_augmentation_weak k t ht

/-- The actual augmentation is original Joyal weak at every original
simplex-category parameter, with no geometric hypothesis. -/
theorem augmentation_weak (k : SimplexCategory) :
    weakCategoricalEquivalences (JTCylinderFrame.augmentation.app k) := by
  induction k using SimplexCategory.rec with | h n =>
    exact augmentation_nat_weak n

/-- The actual cylinder-to-CE comparison is original Joyal weak. -/
theorem toCE_weak (k : SimplexCategory) :
    weakCategoricalEquivalences (JTCylinderCEComparison.valueComparison.app k) :=
  JTCylinderMappingWeak.toCE_weak augmentation_weak k

/-- The actual cylinder-to-original-cone comparison is original Joyal weak. -/
theorem toCone_weak (k : SimplexCategory) :
    weakCategoricalEquivalences (JTCylinderConeComparison.comparison.app k) :=
  JTCylinderMappingWeak.toCone_weak augmentation_weak k

/-- The SAME chosen ordinary unit induces a Kan weak map on actual CE
Hom. Both original geometric frame inputs have now been supplied. -/
theorem etaCE_GW (W : SegalLocalizers.ReverseDaggerSpace.{0})
    (x y : (chosenT W).toSSet.obj (op ⦋0⦌)) :
    DaggerSSetGluing.GW
      (JTCEPlainMappingTarget.plainCEHomMap (etaUnder W x y)) :=
  JTCEUnitCylinderCriterion.etaCE_GW_of_cylinder_augmentation
    augmentation_weak W x y

end

end DaggerModels.PartII.JTCylinderAugmentationWeak
