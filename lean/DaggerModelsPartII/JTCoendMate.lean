import DaggerModelsPartII.JTCoendComparison
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# The right mate of the actual coend comparison

The comparison is conjugated through the constructed frame adjunction and
the composite of the original dagger JT and Part I adjunctions. This gives
the actual natural comparison of right adjoints, with its unit and counit
identities. No global isomorphism of these right adjoints is asserted.
-/

set_option autoImplicit false

open CategoryTheory DaggerModels

namespace DaggerModels.PartII.JTCoendMate

open DaggerJTRealization
open OrdinaryRigidification.DaggerRigidification OrdinaryRigidification.DaggerNerve

noncomputable section

/-- The right adjoint of the original composite rigidified JT realization. -/
def compositeNerve : DaggerSimplicialCat.{0, 0} ⥤
    SegalLocalizers.ReverseDaggerSpace.{0} :=
  daggerCoherentNerve ⋙ DaggerJTAdjunction.daggerNerve

/-- The composite adjunction uses the original rigidification and JT functors. -/
def compositeAdjunction : daggerRealization ⋙ daggerRigidification ⊣ compositeNerve :=
  DaggerJTAdjunction.adjunction.comp DaggerActualRigidificationQuillen.adjunction

/-- The manuscript's right mate of the capital coend comparison. -/
def rightMate : compositeNerve ⟶ JTFrameAdjunction.frameNerve :=
  conjugateEquiv compositeAdjunction JTFrameAdjunction.adjunction
    JTCoendComparison.comparison

/-- The right comparison is exactly conjugate to the constructed left comparison. -/
theorem rightMate_conjugate :
    (conjugateEquiv compositeAdjunction JTFrameAdjunction.adjunction).symm rightMate =
      JTCoendComparison.comparison :=
  (conjugateEquiv compositeAdjunction JTFrameAdjunction.adjunction).symm_apply_apply _

/-- The mate identity at the units of the two actual adjunctions. -/
theorem unit_rightMate (W : SegalLocalizers.ReverseDaggerSpace.{0}) :
    compositeAdjunction.unit.app W ≫
      rightMate.app (daggerRigidification.obj (daggerRealization.obj W)) =
        JTFrameAdjunction.adjunction.unit.app W ≫
          JTFrameAdjunction.frameNerve.map (JTCoendComparison.comparison.app W) :=
  unit_conjugateEquiv compositeAdjunction JTFrameAdjunction.adjunction
    JTCoendComparison.comparison W

/-- The mate identity at the counits, for the literal dagger-category target. -/
theorem rightMate_counit (C : DaggerSimplicialCat.{0, 0}) :
    JTFrameAdjunction.frameRealization.map (rightMate.app C) ≫
      JTFrameAdjunction.adjunction.counit.app C =
        JTCoendComparison.comparison.app (compositeNerve.obj C) ≫
          compositeAdjunction.counit.app C :=
  conjugateEquiv_counit compositeAdjunction JTFrameAdjunction.adjunction
    JTCoendComparison.comparison C

end

end DaggerModels.PartII.JTCoendMate
