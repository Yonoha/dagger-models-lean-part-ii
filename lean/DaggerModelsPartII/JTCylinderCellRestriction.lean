import DaggerModelsPartII.JTCylinderCellQuotient
import DaggerModelsPartII.JTCylinderQuotientImages

/-!
# The same augmentation on the actual quotient cell images

The native range of the literal cell embedding equals the specified
quotient image of the original staircase simplex. This transports the
already proved weak block augmentation to precisely those subcomplexes
used in the actual cylinder cover and adjacent-intersection theorem.
-/

set_option autoImplicit false

open CategoryTheory Simplicial

namespace DaggerModels.PartII.JTCylinderCellRestriction

open JTCylinderCellQuotient JTCylinderStaircase JTCylinderQuotientImages

noncomputable section

/-- The actual embedding range is the same specified quotient cell. -/
theorem cell_range_eq_quotientImage (k : ℕ) (t : Fin (k + 1)) :
    SSet.Subcomplex.range (cellToCylinder k t) = quotientImage k t := by
  rw [cellToCylinder_range]
  unfold blockSimplexToCylinder
  rw [SSet.Subcomplex.range_comp,
    SSet.Subcomplex.range_eq_top, SSet.Subcomplex.image_top,
    SSet.Subcomplex.range_comp]
  change (SSet.Subcomplex.range (staircaseSimplex k t)).image
      (JTCylinderFrame.cylinder ⦋k⦌) =
    (staircaseImage k t).image (JTCylinderFrame.cylinder ⦋k⦌)
  rw [SSet.Subcomplex.range_eq_ofSimplex]
  rfl

/-- Each subcomplex in the actual quotient cover is weak over the SAME
original interval augmentation. -/
theorem quotientImage_augmentation_weak (k : ℕ) (t : Fin (k + 1)) :
    DaggerNativeJoyalMappingTest.weakCategoricalEquivalences
      ((quotientImage k t).ι ≫ JTCylinderFrame.augmentation.app ⦋k⦌) := by
  rw [← cell_range_eq_quotientImage]
  exact cellRange_augmentation_weak k t

end

end DaggerModels.PartII.JTCylinderCellRestriction
