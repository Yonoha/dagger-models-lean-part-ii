import OrdinaryJTRightNerveKan
import OrdinaryJTRightNerveSegal
import OrdinaryJTRightNerveCompleteness
import DaggerModelsPartII.JTRawOrdinaryAdjoint

/-!
# The literal raw target of the ordinary JT transpose

The ordinary right-nerve properties apply to the exact target of
`JTRawOrdinaryAdjoint.gRawTilde`. They require no locality hypothesis on `W`.
These properties alone do not assert that the raw transpose is weak.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Simplicial HomotopicalAlgebra DaggerModels

namespace DaggerModels.PartII.RawOrdinaryJTRightNerve

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

/-- The exact target of the raw transpose has an underlying quasicategory. -/
theorem rawTarget_quasicategory (W : Source) :
    (JTRawFreeInnerComparison.rawTarget W).toSSet.Quasicategory :=
  JTFreeInnerFactorization.replacement_underlying_quasicategory
    (DaggerJTRealization.daggerRealization.obj W)

/-- Every row of the ordinary right nerve at the raw transpose's target is Kan. -/
theorem rawTarget_row_kan (W : Source) (m : SimplexCategory) :
    (JTRightAdjointOrderedFiber.ordinaryRow
      (JTRawFreeInnerComparison.rawTarget W).toSSet m).KanComplex := by
  letI := rawTarget_quasicategory W
  exact OrdinaryJTRightNerveKan.ordinaryRow_kan _ m

/-- The literal spine restriction of each raw-target right-nerve row is Kan weak. -/
theorem rawTarget_spine_weak (W : Source) (n : ℕ) :
    DaggerSSetGluing.GW
      (OrdinaryJTRightNerveSegal.spineRestriction
        (JTRawFreeInnerComparison.rawTarget W).toSSet n) := by
  letI := rawTarget_quasicategory W
  exact OrdinaryJTRightNerveSegal.spineRestriction_weak _ n

/-- The walking restriction of the same raw-target right nerve is Kan weak. -/
theorem rawTarget_walking_weak (W : Source) :
    DaggerSSetGluing.GW
      (OrdinaryJTRightNerveCompleteness.walkingRestriction
        (JTRawFreeInnerComparison.rawTarget W).toSSet) := by
  letI := rawTarget_quasicategory W
  exact OrdinaryJTRightNerveCompleteness.walkingRestriction_weak _

#print axioms rawTarget_quasicategory
#print axioms rawTarget_row_kan
#print axioms rawTarget_spine_weak
#print axioms rawTarget_walking_weak

end
end DaggerModels.PartII.RawOrdinaryJTRightNerve
