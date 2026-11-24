import OrdinaryJTLocality
import OrdinaryJoyalFibrancy
import DaggerModelsPartII.LeftLocalizedQuillenDescent

/-!
# The actual ordinary JT Quillen adjunction after CSS localization

The existing `leftLocalizedQuillen_of_rightFibrantLocal` theorem descends
the checked injective Kan base adjunction because the actual right nerve
of every original Joyal fibrant object passes the exact ordinary CSS tests.
This is a Quillen adjunction; its Quillen-equivalence criterion and actual
ordered derived-unit weakness remain separate proof obligations.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory HomotopicalAlgebra

namespace DaggerModels.PartII.OrdinaryJTCSSQuillen

open OrdinaryCSSLocalization (Space)
open OrdinaryJTProjectiveQuillen (joyalModel)
open OrdinaryJTCurriedAdjunction (left right adjunction)

noncomputable section

/-- The original ordinary JT realization and right nerve are Quillen for
the exact ordinary CSS localization and the original ordinary Joyal model. -/
theorem isQuillenAdjunction :
    @Adjunction.IsQuillenAdjunction Space SSet.{0} _ _
      OrdinaryCSSLocalization.model joyalModel left right adjunction := by
  apply Localization.leftLocalizedQuillen_of_rightFibrantLocal
    OrdinarySpaceReedyInjective.injectiveModel joyalModel
    OrdinaryCSSLocalization.localizingFamily OrdinaryCSSLocalization.model
    OrdinaryCSSLocalization.exactClasses.1 OrdinaryCSSLocalization.exactClasses.2
    left right adjunction OrdinarySpaceReedyInjective.isQuillenAdjunction
  intro X hX
  letI : X.Quasicategory :=
    (OrdinaryJoyalFibrancy.isFibrant_iff_quasicategory X).mp hX
  exact OrdinaryJTLocality.right_obj_localObject X

#print axioms isQuillenAdjunction

end

end DaggerModels.PartII.OrdinaryJTCSSQuillen
