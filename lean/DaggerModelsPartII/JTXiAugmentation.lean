import DaggerModelsPartII.JTXiFaceCofibration
import DaggerModelsPartII.JTEndpointFrames
import DaggerModelsPartII.JTEndpointCobaseComparison
import DaggerModelsPartII.JTXiCoefficientEndpointIso

/-!
# Weak augmentation of the original Xi endpoint collapse

The actual Xi attaching arrows are cofibrations in the original dagger
coefficient model. Original left properness and the retained weak Xi
augmentation components give a weak augmentation of its literal endpoint
cobase. The comparison induced by the actual zero-fixed replacement qX is
then weak by two-out-of-three and fixes the original ordered boundary.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.JTXiAugmentation

open JTRelativeReedyFrame JTActualCosimplicialFrame JTEndpointCofibrancy
open JTEndpointArrowReplacement JTEndpointAugmentations JTEndpointCobaseAugmentations
open JTEndpointHom JTEndpointObjects JTEndpointFrames

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

/-- The original Xi arrow augmentation, with the same ordered iota. -/
def XiArrowAugmentation :
    X ⟶ (Functor.const SimplexCategory).obj (Arrow.mk iota) :=
  arrowAugmentation XiAugmentationCurried

/-- The induced augmentation of the literal raw coefficient collapse. -/
def XiCobaseAugmentation :
    collapsedFrame XiAugmentationCurried ⟶
      (Functor.const SimplexCategory).obj Jdagger :=
  cobaseAug XiArrowAugmentation

/-- The original boundary is retained by the raw Xi augmentation. -/
theorem boundary_XiCobaseAugmentation :
    JTEndpointCobase.endpointCobase_inl (endpointFaces XiCurried)
        Bdagger (endpointCollapse XiAugmentationCurried) ≫ XiCobaseAugmentation =
      (Functor.const SimplexCategory).map iota :=
  boundary_cobaseAug XiArrowAugmentation

/-- Each component of the actual raw Xi augmentation is original weak. -/
theorem XiCobaseAugmentation_weak (k : SimplexCategory) :
    weakEquivalences Coefficient (XiCobaseAugmentation.app k) := by
  apply cobaseAug_weak XiArrowAugmentation
  · intro j
    exact JTXiFaceCofibration.endpointFaces_cof j
  · intro j
    exact xi_source_weak j
  · intro j
    exact xi_target_weak j

/-- The original raw Xi collapse under its fixed ordered boundary. -/
def XiFrame : SimplexCategory ⥤ Under Bdagger :=
  underDiagram XiArrowAugmentation

/-- This is the original collapsed Xi under-diagram, with its specified
boundary coprojection and without replacing its target. -/
theorem XiFrame_eq : XiFrame = collapsedUnder XiAugmentationCurried := rfl

/-- The same augmentation as a map under the literal ordered boundary. -/
def XiFrameAugmentation :
    XiFrame ⟶ (Functor.const SimplexCategory).obj (Under.mk iota) :=
  underAugmentation XiArrowAugmentation

/-- Each component of this exact under-boundary augmentation is weak. -/
theorem XiFrameAugmentation_weak (k : SimplexCategory) :
    weakEquivalences (Under Bdagger) (XiFrameAugmentation.app k) := by
  change weakEquivalences Coefficient (XiCobaseAugmentation.app k)
  exact XiCobaseAugmentation_weak k

/-- The actual qX induces the manuscript's raw endpoint-cobase comparison. -/
def QXToXi : QXFrame ⟶ XiFrame :=
  JTEndpointCobaseComparison.underComparison qX QXaugmentation
    XiArrowAugmentation rfl

/-- This specified qX cobase map preserves the augmentation to original iota. -/
theorem QXToXi_augmentation :
    QXToXi ≫ XiFrameAugmentation = QXFrameAugmentation :=
  JTEndpointCobaseComparison.underComparison_augmentation qX
    QXaugmentation XiArrowAugmentation rfl

/-- The actual qX cobase comparison is a weak equivalence in every degree. -/
theorem QXToXi_weak (k : SimplexCategory) :
    weakEquivalences (Under Bdagger) (QXToXi.app k) := by
  apply (weakEquivalences (Under Bdagger)).of_postcomp _
    (XiFrameAugmentation.app k) (XiFrameAugmentation_weak k)
  rw [show QXToXi.app k ≫ XiFrameAugmentation.app k =
    QXFrameAugmentation.app k from NatTrans.congr_app QXToXi_augmentation k]
  exact QXFrameAugmentation_weak k

/-- The actual replacement-induced comparison is weak in the native
opposite Reedy model, with the original ordered boundary. -/
theorem QXToXi_reedyWeak :
    weakEquivalences (SimplexCategoryᵒᵖ ⥤ (Under Bdagger)ᵒᵖ)
      (NatTrans.op QXToXi) := by
  intro k
  rw [weakEquivalences_op]
  exact QXToXi_weak k.unop

end

end DaggerModels.PartII.JTXiAugmentation
