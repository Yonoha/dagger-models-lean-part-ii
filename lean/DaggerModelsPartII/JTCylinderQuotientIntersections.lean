import DaggerModelsPartII.JTCylinderQuotientImages
import DaggerModelsPartII.MonoPushoutSubcomplexImages
import NativeMonoRestrictionParameterizedWalkingLifting

/-!
# Intersections of actual reduced-cylinder staircase images

The ordered endpoint representative lies in every maximal prism cell.
The actual reduced-cylinder pushout therefore preserves the intersections
of the specified cell images. The adjacent intersection in the quotient
is the image of the previously proved adjacent intersection in the
uncollapsed prism. No smaller block-quotient identification is asserted.
-/

set_option autoImplicit false

open CategoryTheory Limits Simplicial MonoidalCategory

namespace DaggerModels.PartII.JTCylinderQuotientIntersections

open JTXiEndpointCollapse JTCylinderStaircase
open JTCylinderQuotientImages

noncomputable section

private instance cylinderInclusion_mono (k : ℕ) :
    Mono ((ReducedCylinder.tensorInclusion JTCylinderFrame.j).app
      (Δ[k] : SSet.{0})) := by
  change Mono (JTCylinderFrame.j ▷ (Δ[k] : SSet.{0}))
  exact DaggerNativeMonoRestrictionParameterizedWalkingLifting.right_tensor_mono
    JTCylinderFrame.j (Δ[k] : SSet.{0})

/-- The quotient images of any two specified maximal cells have their
literal intersection equal to the image of the source intersection. -/
theorem quotientImage_inf (k : ℕ) (s t : Fin (k + 1)) :
    (staircaseImage k s ⊓ staircaseImage k t).image
        (JTCylinderFrame.cylinder ⦋k⦌) =
      quotientImage k s ⊓ quotientImage k t := by
  change (staircaseImage k s ⊓ staircaseImage k t).image
      (JTCylinderFrame.cylinder ⦋k⦌) =
    (staircaseImage k s).image (JTCylinderFrame.cylinder ⦋k⦌) ⊓
      (staircaseImage k t).image (JTCylinderFrame.cylinder ⦋k⦌)
  exact MonoPushoutSubcomplexImages.image_inf_eq
    (JTCylinderFrame.isPushout ⦋k⦌)
    (endpointRepresentative k) (endpointRepresentative_quotient k)
    (staircaseImage k s) (staircaseImage k t)
    (endpointRepresentative_range_le k s)
    (endpointRepresentative_range_le k t)

/-- All earlier quotient cells at a chosen cut, with the same strict
index inequality used by the uncollapsed staircase theorem. -/
def previousQuotient (k : ℕ) (t : Fin (k + 1)) :
    (JTCylinderFrame.value.obj ⦋k⦌).Subcomplex :=
  ⨆ s : {s : Fin (k + 1) // s.val < t.val}, quotientImage k s.val

/-- The previous quotient union is the actual image of the previous
uncollapsed union, by image preservation of this supremum. -/
theorem previousQuotient_eq_image (k : ℕ) (t : Fin (k + 1)) :
    previousQuotient k t =
      (previous k t).image (JTCylinderFrame.cylinder ⦋k⦌) := by
  simp only [previousQuotient, previous, quotientImage,
    SSet.Subcomplex.image_iSup]

private theorem endpointRepresentative_range_le_previous (k : ℕ)
    (t : Fin (k + 1)) (ht : 0 < t.val) :
    SSet.Subcomplex.range (endpointRepresentative k) ≤ previous k t := by
  let p : Fin (k + 1) := ⟨t.val - 1, by omega⟩
  have hp : p.val < t.val := by dsimp [p]; omega
  have hle : staircaseImage k p ≤ previous k t := by
    exact le_iSup_of_le ⟨p, hp⟩ le_rfl
  exact (endpointRepresentative_range_le k p).trans hle

/-- The image-intersection identity also applies to the new cell and
the whole union of earlier cells, because the common boundary representative
lies in an earlier cell whenever the cut is positive. -/
private theorem quotientImage_inf_previous (k : ℕ)
    (t : Fin (k + 1)) (ht : 0 < t.val) :
    (staircaseImage k t ⊓ previous k t).image
        (JTCylinderFrame.cylinder ⦋k⦌) =
      quotientImage k t ⊓ previousQuotient k t := by
  rw [previousQuotient_eq_image]
  change (staircaseImage k t ⊓ previous k t).image
      (JTCylinderFrame.cylinder ⦋k⦌) =
    (staircaseImage k t).image (JTCylinderFrame.cylinder ⦋k⦌) ⊓
      (previous k t).image (JTCylinderFrame.cylinder ⦋k⦌)
  exact MonoPushoutSubcomplexImages.image_inf_eq
    (JTCylinderFrame.isPushout ⦋k⦌)
    (endpointRepresentative k) (endpointRepresentative_quotient k)
    (staircaseImage k t) (previous k t)
    (endpointRepresentative_range_le k t)
    (endpointRepresentative_range_le_previous k t ht)

/-- The actual adjacent reduced-cylinder quotient cell meets all
preceding quotient cells exactly in its intersection with the immediately
preceding quotient cell. The result includes every positive cut. -/
theorem quotientImage_adjacent (k : ℕ) (t : Fin (k + 1))
    (ht : 0 < t.val) :
    quotientImage k t ⊓ previousQuotient k t =
      quotientImage k t ⊓ quotientImage k ⟨t.val - 1, by omega⟩ := by
  let p : Fin (k + 1) := ⟨t.val - 1, by omega⟩
  change quotientImage k t ⊓ previousQuotient k t =
    quotientImage k t ⊓ quotientImage k p
  calc
    quotientImage k t ⊓ previousQuotient k t =
        (staircaseImage k t ⊓ previous k t).image
          (JTCylinderFrame.cylinder ⦋k⦌) :=
      (quotientImage_inf_previous k t ht).symm
    _ = (staircaseImage k t ⊓ staircaseImage k p).image
          (JTCylinderFrame.cylinder ⦋k⦌) := by
      exact congrArg
        (fun A : ((Δ[1] : SSet.{0}) ⊗ Δ[k]).Subcomplex ↦
          A.image (JTCylinderFrame.cylinder ⦋k⦌))
        (staircase_adjacent k t ht)
    _ = quotientImage k t ⊓ quotientImage k p := quotientImage_inf k t p

end

end DaggerModels.PartII.JTCylinderQuotientIntersections
