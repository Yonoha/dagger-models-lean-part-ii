import OrdinaryJTLocality
import RawOrdinaryJTRightNerve

/-!
# CSS fibrancy of the literal raw ordinary JT target

The checked ordinary right-nerve locality theorem applies to the actual
underlying quasicategory of the unchanged raw target. This imposes no
completeness or fibrancy condition on the original reversal-space input.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory HomotopicalAlgebra

namespace DaggerModels.PartII.RawOrdinaryJTTargetCSSFibrant

open OrdinaryCSSLocalization (Space)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

/-- The exact target of the original raw transpose is fibrant in the
actual ordinary CSS localization for every original input. -/
theorem rawTarget_cssFibrant (W : Source) :
    @IsFibrant Space _ OrdinaryCSSLocalization.model.categoryWithFibrations _
      (OrdinaryJTCurriedAdjunction.right.obj
        (JTRawFreeInnerComparison.rawTarget W).toSSet) := by
  letI : (JTRawFreeInnerComparison.rawTarget W).toSSet.Quasicategory :=
    RawOrdinaryJTRightNerve.rawTarget_quasicategory W
  exact OrdinaryJTLocality.right_obj_css_isFibrant _

#print axioms rawTarget_cssFibrant

end
end DaggerModels.PartII.RawOrdinaryJTTargetCSSFibrant
