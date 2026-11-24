import DaggerModelsPartII.JTFrameAdjunction
import DaggerModelsPartII.JTRelativeReedyFrameProperties

/-!
# The actual coend comparison of the relative JT frames

The full two-index frame comparison induces a natural transformation from
the constructed frame realization to the original dagger JT realization
followed by the Part I rigidification. The Yoneda left Kan extension
universal property fixes its action on represented generators.

This file constructs the underived comparison. Its weak-equivalence
property on projectively cofibrant inputs is a separate assertion.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Simplicial DaggerModels

namespace DaggerModels.PartII.JTCoendComparison

open DaggerJTAdjunction JTRelativeReedyFrame RigidifiedJTFrames
open OrdinaryRigidification.DaggerRigidification

noncomputable section

local instance : HasColimits Coefficient := daggerSimplicialCatHasColimits

local instance : ModelCategory Coefficient :=
  DaggerActualRigidificationQuillen.modelG.{0}

local instance : JTFrameAdjunction.presheafRealization.IsLeftKanExtension
    (uliftYoneda.{0}.leftKanExtensionUnit JTFrameAdjunction.frameParameter) := by
  dsimp [JTFrameAdjunction.presheafRealization]
  infer_instance

/-- The actual lower-case comparison with both original indices uncurried. -/
def parameterComparison : JTFrameAdjunction.frameParameter ⟶ Xi :=
  Functor.uncurry.map comparisonOuter ≫ (Functor.currying.counitIso.app Xi).hom

/-- Uncurrying introduces no extra automorphism on a frame component. -/
theorem parameterComparison_app (m : ReverseSimplex) (k : SimplexCategory) :
    parameterComparison.app (m, k) = (comparison.app k).app m := by
  change (comparison.app k).app m ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The prescribed zero component remains literally the identity. -/
theorem parameterComparison_zero (m : ReverseSimplex) :
    parameterComparison.app (m, ⦋0⦌) = 𝟙 (Xi.obj (m, ⦋0⦌)) := by
  rw [parameterComparison_app]
  rfl

/-- The same original rigidified realization on the uncurried presheaf category. -/
def presheafTarget : (DaggerIndexᵒᵖ ⥤ Type) ⥤ Coefficient :=
  DaggerJTAdjunction.presheafRealization ⋙ daggerRigidification

/-- The parameter comparison as a cocone into the actual target realization. -/
def parameterComparisonToTarget :
    JTFrameAdjunction.frameParameter ⟶ uliftYoneda.{0} ⋙ presheafTarget :=
  parameterComparison ≫
    (Functor.associator uliftYoneda.{0}
      DaggerJTAdjunction.presheafRealization daggerRigidification).hom

/-- The induced comparison is the native Yoneda left Kan extension descent. -/
def presheafComparison : JTFrameAdjunction.presheafRealization ⟶ presheafTarget :=
  JTFrameAdjunction.presheafRealization.descOfIsLeftKanExtension
    (uliftYoneda.{0}.leftKanExtensionUnit JTFrameAdjunction.frameParameter)
    presheafTarget parameterComparisonToTarget

/-- The coend comparison has exactly the prescribed represented-generator action. -/
theorem presheafComparison_fac :
    uliftYoneda.{0}.leftKanExtensionUnit JTFrameAdjunction.frameParameter ≫
      Functor.whiskerLeft uliftYoneda.{0} presheafComparison =
        parameterComparisonToTarget :=
  Functor.descOfIsLeftKanExtension_fac _ _ _ _

/-- Component form of the represented-generator normalization. -/
theorem presheafComparison_fac_app (p : DaggerIndex) :
    (uliftYoneda.{0}.leftKanExtensionUnit JTFrameAdjunction.frameParameter).app p ≫
      presheafComparison.app (uliftYoneda.{0}.obj p) =
        parameterComparisonToTarget.app p :=
  NatTrans.congr_app presheafComparison_fac p

/-- In the literal target frame the generator equation is the original comparison. -/
theorem presheafComparison_fac_app_eq (p : DaggerIndex) :
    (uliftYoneda.{0}.leftKanExtensionUnit JTFrameAdjunction.frameParameter).app p ≫
      presheafComparison.app (uliftYoneda.{0}.obj p) = parameterComparison.app p := by
  have h := presheafComparison_fac_app p
  change _ = parameterComparison.app p ≫ 𝟙 _ at h
  simpa only [Category.comp_id] using h

/-- On represented two-index generators the coend comparison is a weak equivalence. -/
theorem presheafComparison_represented_weak (m : ReverseSimplex) (n : ℕ) :
    weakEquivalences Coefficient
      (presheafComparison.app (uliftYoneda.{0}.obj (m, ⦋n⦌))) := by
  let η := uliftYoneda.{0}.leftKanExtensionUnit JTFrameAdjunction.frameParameter
  have hη : weakEquivalences Coefficient (η.app (m, ⦋n⦌)) :=
    (weakEquivalence_iff _).mp inferInstance
  apply (weakEquivalences Coefficient).of_precomp (η.app (m, ⦋n⦌)) _ hη
  rw [presheafComparison_fac_app_eq, parameterComparison_app]
  exact comparison_component_weak m n

/-- The generator equation uniquely determines the whole comparison. -/
theorem presheafComparison_unique
    (α : JTFrameAdjunction.presheafRealization ⟶ presheafTarget)
    (hα : uliftYoneda.{0}.leftKanExtensionUnit JTFrameAdjunction.frameParameter ≫
      Functor.whiskerLeft uliftYoneda.{0} α = parameterComparisonToTarget) :
    α = presheafComparison := by
  apply Functor.hom_ext_of_isLeftKanExtension _
    (uliftYoneda.{0}.leftKanExtensionUnit JTFrameAdjunction.frameParameter)
  exact hα.trans presheafComparison_fac.symm

/-- The target is canonically the original two-stage realization. -/
def targetIso :
    sourceEquivalence.functor ⋙ presheafTarget ≅
      DaggerJTRealization.daggerRealization ⋙ daggerRigidification :=
  (Functor.associator sourceEquivalence.functor
    DaggerJTAdjunction.presheafRealization daggerRigidification).symm ≪≫
      Functor.isoWhiskerRight DaggerJTAdjunction.realizationIso daggerRigidification

/-- The manuscript's capital coend comparison, natural in the original source. -/
def comparison : JTFrameAdjunction.frameRealization ⟶
    DaggerJTRealization.daggerRealization ⋙ daggerRigidification :=
  Functor.whiskerLeft sourceEquivalence.functor presheafComparison ≫ targetIso.hom

/-- Naturality holds for every morphism of reversal simplicial spaces. -/
theorem comparison_naturality {W V : SegalLocalizers.ReverseDaggerSpace.{0}}
    (f : W ⟶ V) :
    JTFrameAdjunction.frameRealization.map f ≫ comparison.app V =
      comparison.app W ≫ daggerRigidification.map
        (DaggerJTRealization.daggerRealization.map f) :=
  comparison.naturality f

end

end DaggerModels.PartII.JTCoendComparison
