import DaggerModelsPartII.JTEndpointFrames
import DaggerModelsPartII.JTEndpointCofibrancy
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-!
# Degree-zero normalization of the actual endpoint frames

The actual Xi arrow augmentation in degree zero is the checked ordered
isomorphism to the original boundary inclusion. The fixed-zero equations
give the same statement for both replacements. Cobase change along the
source isomorphism makes the frame coprojection invertible, so the
augmentation under the original boundary is invertible at degree zero.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Simplicial DaggerModels

namespace DaggerModels.PartII.JTEndpointFrameZero

open JTEndpointHom JTEndpointMateUnder JTEndpointCofibrancy
open JTEndpointArrowReplacement JTEndpointAugmentations
open JTEndpointCobaseAugmentations JTEndpointFrames
open JTRelativeReedyFrame JTActualCosimplicialFrame JTZeroObjects
open JTEndpointObjects

noncomputable section

private local instance : HasLimits Coefficient := daggerSimplicialCatHasLimits
private local instance : HasColimits Coefficient := daggerSimplicialCatHasColimits
private local instance : ModelCategory Coefficient :=
  DaggerActualRigidificationQuillen.modelG.{0}

private theorem xiAugmentation_zero_at (m : ReverseSimplex) :
    (XiAugmentationCurried.app ⦋0⦌).app m =
      (RigidifiedJTFrames.XiZeroIso.app m).hom := by
  change JTFrameProjection.XiAugmentation.app (m, ⦋0⦌) =
    (RigidifiedJTFrames.XiZeroIso.app m).hom
  exact JTFrameProjection.XiAugmentation_zero m

/-- The original Xi endpoint-arrow augmentation is the canonical ordered
arrow isomorphism to the literal boundary inclusion in degree zero. -/
theorem xiArrowAugmentation_zero :
    (arrowAugmentation XiAugmentationCurried).app ⦋0⦌ =
      zeroArrowIso.hom := by
  apply Arrow.hom_ext
  · change (endpointCollapse XiAugmentationCurried).app ⦋0⦌ =
      sourceZeroIso.hom
    apply coprod.hom_ext
    · simpa [endpointCollapse, sourceZeroIso, endpointCoproductIso]
        using congrArg (fun f ↦ f ≫ endpointMap 0)
          (xiAugmentation_zero_at zeroIndex)
    · simpa [endpointCollapse, sourceZeroIso, endpointCoproductIso]
        using congrArg (fun f ↦ f ≫ endpointMap 1)
          (xiAugmentation_zero_at zeroIndex)
  · change (XiAugmentationCurried.app ⦋0⦌).app
        JTOrderedFrameMate.oneIndex ≫ _ = targetZeroIso.hom
    rw [xiAugmentation_zero_at JTOrderedFrameMate.oneIndex]
    rfl

/-- The Gamma augmentation is the same ordered isomorphism in degree zero
because the literal comparison is fixed there. -/
theorem gammaArrowAugmentation_zero :
    (arrowAugmentation augmentation).app ⦋0⦌ =
      zeroArrowIso.hom := by
  have h := NatTrans.congr_app lambda_augmentation ⦋0⦌
  have h' : (arrowAugmentation XiAugmentationCurried).app ⦋0⦌ =
      (arrowAugmentation augmentation).app ⦋0⦌ := by
    simpa only [NatTrans.comp_app, lambda_zero, Category.id_comp] using h
  exact h'.symm.trans xiArrowAugmentation_zero

/-- The first replacement has the exact original ordered arrow isomorphism
as its degree-zero augmentation. -/
theorem QGaugmentation_zero :
    QGaugmentation.app ⦋0⦌ = zeroArrowIso.hom := by
  simpa only [QGaugmentation, NatTrans.comp_app, qG_zero,
    Category.id_comp] using gammaArrowAugmentation_zero

/-- The second replacement has the same degree-zero arrow isomorphism. -/
theorem QXaugmentation_zero :
    QXaugmentation.app ⦋0⦌ = zeroArrowIso.hom := by
  simpa only [QXaugmentation, NatTrans.comp_app, qX_zero,
    Category.id_comp] using xiArrowAugmentation_zero

private theorem cobaseAug_zero_isIso
    {F : SimplexCategory ⥤ Arrow Coefficient}
    (a : F ⟶ (Functor.const SimplexCategory).obj (Arrow.mk iota))
    [IsIso (a.app ⦋0⦌)] : IsIso ((cobaseAug a).app ⦋0⦌) := by
  haveI : IsIso ((sourceAug a).app ⦋0⦌) := by
    change IsIso (a.app ⦋0⦌).left
    infer_instance
  haveI : IsIso ((targetAug a).app ⦋0⦌) := by
    change IsIso (a.app ⦋0⦌).right
    infer_instance
  let h := JTEndpointCobase.endpointCobase_isPushout_at
    (structureMap F) Bdagger (sourceAug a) ⦋0⦌
  haveI : IsIso ((frameInclusion a).app ⦋0⦌ ≫ h.isoPushout.hom) := by
    change IsIso ((JTEndpointCobase.endpointCobase_inr
      (structureMap F) Bdagger (sourceAug a)).app ⦋0⦌ ≫ h.isoPushout.hom)
    rw [h.inr_isoPushout_hom]
    infer_instance
  haveI : IsIso ((frameInclusion a).app ⦋0⦌) :=
    IsIso.of_isIso_comp_right _ h.isoPushout.hom
  haveI : IsIso
      ((frameInclusion a).app ⦋0⦌ ≫ (cobaseAug a).app ⦋0⦌) := by
    rw [show (frameInclusion a).app ⦋0⦌ ≫ (cobaseAug a).app ⦋0⦌ =
      (targetAug a).app ⦋0⦌ from
        NatTrans.congr_app (frameInclusion_cobaseAug a) ⦋0⦌]
    infer_instance
  exact IsIso.of_isIso_comp_left ((frameInclusion a).app ⦋0⦌)
    ((cobaseAug a).app ⦋0⦌)

/-- The actual first endpoint-frame augmentation is an isomorphism at
degree zero, under the original boundary. -/
theorem QGFrameAugmentation_zero_isIso :
    IsIso (QGFrameAugmentation.app ⦋0⦌) := by
  haveI : IsIso (QGaugmentation.app ⦋0⦌) := by
    rw [QGaugmentation_zero]
    infer_instance
  haveI : IsIso ((Under.forget Bdagger).map
      (QGFrameAugmentation.app ⦋0⦌)) := by
    change IsIso ((cobaseAug QGaugmentation).app ⦋0⦌)
    exact cobaseAug_zero_isIso QGaugmentation
  exact isIso_of_reflects_iso _ (Under.forget Bdagger)

/-- The actual second endpoint-frame augmentation has the same literal
degree-zero isomorphism. -/
theorem QXFrameAugmentation_zero_isIso :
    IsIso (QXFrameAugmentation.app ⦋0⦌) := by
  haveI : IsIso (QXaugmentation.app ⦋0⦌) := by
    rw [QXaugmentation_zero]
    infer_instance
  haveI : IsIso ((Under.forget Bdagger).map
      (QXFrameAugmentation.app ⦋0⦌)) := by
    change IsIso ((cobaseAug QXaugmentation).app ⦋0⦌)
    exact cobaseAug_zero_isIso QXaugmentation
  exact isIso_of_reflects_iso _ (Under.forget Bdagger)

end

end DaggerModels.PartII.JTEndpointFrameZero
