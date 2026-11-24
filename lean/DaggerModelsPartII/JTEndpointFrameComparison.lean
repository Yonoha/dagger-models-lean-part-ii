import DaggerModelsPartII.JTEndpointFrames
import DaggerModelsPartII.JTEndpointCobaseComparison
import DaggerModelsPartII.StrictFrameMappingWeak

/-!
# The actual weak comparison between the zero-fixed endpoint cobases

The comparison induced by Qlambda fixes the literal ordered boundary and
commutes with the two original augmentations. It is Reedy weak. Mapping
into every original fibrant target under that boundary therefore gives a
weak map of the actual Hom simplicial sets of these Reedy cofibrant cobases.
Identification with the original derived ordered-endpoint mate is separate.
-/

set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTEndpointFrameComparison

open JTRelativeReedyFrame JTEndpointObjects JTEndpointCofibrancy
open JTEndpointArrowReplacement JTEndpointAugmentations JTEndpointFrames

noncomputable section

private local instance : HasLimits Coefficient := daggerSimplicialCatHasLimits
private local instance : HasColimits Coefficient := daggerSimplicialCatHasColimits
private local instance : ModelCategory Coefficient :=
  DaggerActualRigidificationQuillen.modelG.{0}
private local instance : ModelCategory (Under Bdagger) :=
  JTEndpointCobase.underModel Bdagger
private local instance : ModelCategory (Under Bdagger)ᵒᵖ := inferInstance
private local instance : ModelCategory (SimplexCategoryᵒᵖ ⥤ (Under Bdagger)ᵒᵖ) :=
  simplicialReedyModelCategory (Under Bdagger)ᵒᵖ

/-- The actual Qlambda-induced cobase comparison under the ordered boundary. -/
def comparison : QGFrame ⟶ QXFrame :=
  JTEndpointCobaseComparison.underComparison Qlambda QGaugmentation
    QXaugmentation Qlambda_augmentation

/-- This same comparison respects the actual augmentations to iota. -/
theorem comparison_augmentation :
    comparison ≫ QXFrameAugmentation = QGFrameAugmentation :=
  JTEndpointCobaseComparison.underComparison_augmentation Qlambda
    QGaugmentation QXaugmentation Qlambda_augmentation

/-- Every component of the actual boundary-preserving comparison is weak. -/
theorem comparison_weak (k : SimplexCategory) :
    weakEquivalences (Under Bdagger) (comparison.app k) := by
  apply (weakEquivalences (Under Bdagger)).of_postcomp _
    (QXFrameAugmentation.app k) (QXFrameAugmentation_weak k)
  rw [show comparison.app k ≫ QXFrameAugmentation.app k =
    QGFrameAugmentation.app k from NatTrans.congr_app comparison_augmentation k]
  exact QGFrameAugmentation_weak k

/-- The opposite of the actual comparison is weak in the native Reedy model. -/
theorem comparison_reedyWeak :
    weakEquivalences (SimplexCategoryᵒᵖ ⥤ (Under Bdagger)ᵒᵖ)
      (NatTrans.op comparison) := by
  intro k
  rw [weakEquivalences_op]
  exact comparison_weak k.unop

/-- The literal Hom simplicial sets into a specified original target with
its two ordered endpoints. -/
def homSSet (F : SimplexCategory ⥤ Under Bdagger)
    (C : Coefficient) (x y : C.Obj) : SSet.{0} :=
  F.op ⋙ yoneda.obj (JTEndpointHom.targetUnder C x y)

/-- The map obtained by precomposition with the actual collapsed comparison. -/
def precomp (C : Coefficient) (x y : C.Obj) :
    homSSet QXFrame C x y ⟶ homSSet QGFrame C x y :=
  Functor.whiskerRight (NatTrans.op comparison)
    (yoneda.obj (JTEndpointHom.targetUnder C x y))

/-- The actual resolved under-boundary Hom comparison is Kan weak for every
original fibrant target. Derived-mate calibration is not asserted here. -/
theorem precomp_weak (C : Coefficient) [IsFibrant C] (x y : C.Obj) :
    weakEquivalences SSet.{0} (precomp C x y) := by
  letI : IsFibrant QGFrame.op := QGFrame_reedyCofibrant
  letI : IsFibrant QXFrame.op := QXFrame_reedyCofibrant
  letI : IsFibrant (JTEndpointHom.targetUnder C x y) :=
    (UnderReedyCriterion.under_isFibrant_iff Bdagger
      (JTEndpointHom.targetUnder C x y)).2 (by
      change IsFibrant C
      infer_instance)
  exact StrictFrameMappingWeak.strictMapping_map_weak
    (JTEndpointHom.targetUnder C x y) (NatTrans.op comparison) comparison_reedyWeak

end

end DaggerModels.PartII.JTEndpointFrameComparison
