import DaggerModelsPartII.CosimplicialFrameNormalization
import DaggerModelsPartII.JTEndpointFrameComparison
import DaggerModelsPartII.JTEndpointReplacementSquare

/-!
# Localized comparison for the original ordered-endpoint frames

The actual zero-fixed QG and QX endpoint frames compute the same chosen
homotopy mapping object from original iota into the specified ordered
fibrant target. The localized actual Qlambda precomposition is calibrated
to the identity under the canonical frame comparisons. The raw mate remains
pinned by the literal replacement square and the original ordered formula.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTDerivedOrderedMate

open JTRelativeReedyFrame JTEndpointObjects JTEndpointCofibrancy
open JTEndpointFrames JTEndpointHom JTEndpointFrameComparison

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
private local instance : IsFibrant QGFrame.op := QGFrame_reedyCofibrant
private local instance : IsFibrant QXFrame.op := QXFrame_reedyCofibrant

private theorem orderedTarget_fibrant (C : Coefficient) [IsFibrant C]
    (x y : C.Obj) : IsFibrant (targetUnder C x y) :=
  (UnderReedyCriterion.under_isFibrant_iff Bdagger (targetUnder C x y)).2 (by
    change IsFibrant C
    infer_instance)

private theorem QGaugmentation_op_weak :
    weakEquivalences (SimplexCategoryᵒᵖ ⥤ (Under Bdagger)ᵒᵖ)
      (NatTrans.op QGFrameAugmentation) := by
  intro k
  rw [weakEquivalences_op]
  exact QGFrameAugmentation_weak k.unop

private theorem QXaugmentation_op_weak :
    weakEquivalences (SimplexCategoryᵒᵖ ⥤ (Under Bdagger)ᵒᵖ)
      (NatTrans.op QXFrameAugmentation) := by
  intro k
  rw [weakEquivalences_op]
  exact QXFrameAugmentation_weak k.unop

/-- The chosen derived ordered mapping object from the original iota. -/
def orderedMappingObject (C : Coefficient) [IsFibrant C] (x y : C.Obj) :
    (weakEquivalences SSet.{0}).Localization := by
  letI := orderedTarget_fibrant C x y
  exact (homotopyMappingFunctor (targetUnder C x y)).obj (op (Under.mk iota))

/-- Canonical localization comparison for the actual QG endpoint frame. -/
def gammaLocalizationIso (C : Coefficient) [IsFibrant C] (x y : C.Obj) :
    (weakEquivalences SSet.{0}).Q.obj (homSSet QGFrame C x y) ≅
      orderedMappingObject C x y := by
  letI := orderedTarget_fibrant C x y
  exact ((weakEquivalences SSet.{0}).Q.mapIso
    ((StrictFrameMappingWeak.nativeStrictIso (targetUnder C x y)).app QGFrame.op)).symm ≪≫
      frameMappingLocalizationIso (targetUnder C x y)
        (NatTrans.op QGFrameAugmentation) QGaugmentation_op_weak

/-- Canonical localization comparison for the actual QX endpoint frame. -/
def xiLocalizationIso (C : Coefficient) [IsFibrant C] (x y : C.Obj) :
    (weakEquivalences SSet.{0}).Q.obj (homSSet QXFrame C x y) ≅
      orderedMappingObject C x y := by
  letI := orderedTarget_fibrant C x y
  exact ((weakEquivalences SSet.{0}).Q.mapIso
    ((StrictFrameMappingWeak.nativeStrictIso (targetUnder C x y)).app QXFrame.op)).symm ≪≫
      frameMappingLocalizationIso (targetUnder C x y)
        (NatTrans.op QXFrameAugmentation) QXaugmentation_op_weak

/-- The localization of the actual resolved ordered precomposition map. -/
def resolvedOrderedMate (C : Coefficient) [IsFibrant C] (x y : C.Obj) :
    (weakEquivalences SSet.{0}).Q.obj (homSSet QXFrame C x y) ⟶
      (weakEquivalences SSet.{0}).Q.obj (homSSet QGFrame C x y) :=
  (weakEquivalences SSet.{0}).Q.map (precomp C x y)

/-- The actual Qlambda precomposition becomes the identity under the two
canonical comparisons to the same derived ordered mapping object. -/
theorem resolvedOrderedMate_calibration (C : Coefficient) [IsFibrant C]
    (x y : C.Obj) :
    resolvedOrderedMate C x y ≫ (gammaLocalizationIso C x y).hom =
      (xiLocalizationIso C x y).hom := by
  letI := orderedTarget_fibrant C x y
  have h := frameMappingLocalizationIso_naturality (targetUnder C x y)
    (𝟙 (Under.mk iota))
    (NatTrans.op QGFrameAugmentation) (NatTrans.op QXFrameAugmentation)
    QGaugmentation_op_weak QXaugmentation_op_weak
    (NatTrans.op JTEndpointFrameComparison.comparison) (by
      simpa only [NatTrans.op_comp, Functor.map_id, Category.id_comp] using
        congrArg NatTrans.op JTEndpointFrameComparison.comparison_augmentation)
  have hn := congrArg ((weakEquivalences SSet.{0}).Q.map)
    ((StrictFrameMappingWeak.nativeStrictIso (targetUnder C x y)).inv.naturality
      (NatTrans.op JTEndpointFrameComparison.comparison))
  simp only [Functor.map_comp] at hn
  have hprecomp :
      (StrictFrameMappingWeak.strictMapping (targetUnder C x y)).map
        (NatTrans.op JTEndpointFrameComparison.comparison) = precomp C x y := rfl
  rw [hprecomp] at hn
  change (weakEquivalences SSet.{0}).Q.map (precomp C x y) ≫
      ((weakEquivalences SSet.{0}).Q.map
        ((StrictFrameMappingWeak.nativeStrictIso (targetUnder C x y)).inv.app QGFrame.op) ≫
          (frameMappingLocalizationIso (targetUnder C x y)
            (NatTrans.op QGFrameAugmentation) QGaugmentation_op_weak).hom) = _
  rw [← Category.assoc, hn, Category.assoc]
  simpa only [CategoryTheory.op_id, CategoryTheory.Functor.map_id,
    Category.comp_id] using congrArg (fun t ↦ (weakEquivalences SSet.{0}).Q.map
      ((StrictFrameMappingWeak.nativeStrictIso (targetUnder C x y)).inv.app QXFrame.op) ≫ t) h

/-- The exact localized comparison is the specified composite of canonical
frame isomorphisms, so changing a compatible lift does not change it. -/
theorem resolvedOrderedMate_eq (C : Coefficient) [IsFibrant C] (x y : C.Obj) :
    resolvedOrderedMate C x y =
      (xiLocalizationIso C x y).hom ≫ (gammaLocalizationIso C x y).inv := by
  apply (cancel_mono (gammaLocalizationIso C x y).hom).1
  rw [resolvedOrderedMate_calibration, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- The actual resolved ordered comparison is invertible in the Kan localization. -/
theorem resolvedOrderedMate_isIso (C : Coefficient) [IsFibrant C] (x y : C.Obj) :
    IsIso (resolvedOrderedMate C x y) := by
  rw [resolvedOrderedMate_eq]
  infer_instance


/-- The literal comparison from original ordered Xi Hom into its resolved Hom.
No weakness of this raw-to-resolved map is asserted. -/
def xiRawToResolved (C : Coefficient) (x y : C.Obj) :
    JTOrderedFrameMate.XiOrdered C x y ⟶ homSSet QXFrame C x y :=
  (orderedHomSSetIso JTActualCosimplicialFrame.XiAugmentationCurried C x y).inv ≫
    JTEndpointReplacementSquare.QXToXi_precomp C x y

/-- The literal comparison from original ordered Gamma Hom into its resolved Hom.
No weakness of this raw-to-resolved map is asserted. -/
def gammaRawToResolved (C : Coefficient) (x y : C.Obj) :
    JTOrderedFrameMate.GammaOrdered C x y ⟶ homSSet QGFrame C x y :=
  (orderedHomSSetIso JTActualCosimplicialFrame.augmentation C x y).inv ≫
    JTEndpointReplacementSquare.QGToGamma_precomp C x y

/-- The original ordered mate lifts to the actual resolved precomposition,
with the same ordered endpoints and the original replacement maps. -/
theorem orderedMate_resolution_square (C : Coefficient) (x y : C.Obj) :
    JTOrderedFrameMate.orderedMate C x y ≫ gammaRawToResolved C x y =
      xiRawToResolved C x y ≫ precomp C x y := by
  have hraw : JTOrderedFrameMate.orderedMate C x y ≫
      (orderedHomSSetIso JTActualCosimplicialFrame.augmentation C x y).inv =
        (orderedHomSSetIso JTActualCosimplicialFrame.XiAugmentationCurried C x y).inv ≫
          JTEndpointMateUnder.underPrecomp C x y := by
    apply (cancel_mono
      (orderedHomSSetIso JTActualCosimplicialFrame.augmentation C x y).hom).1
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Category.assoc, JTEndpointMateUnder.orderedMate_underPrecomp,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  change JTOrderedFrameMate.orderedMate C x y ≫
      ((orderedHomSSetIso JTActualCosimplicialFrame.augmentation C x y).inv ≫
        JTEndpointReplacementSquare.QGToGamma_precomp C x y) = _
  rw [← Category.assoc, hraw, Category.assoc,
    JTEndpointReplacementSquare.hom_square, ← Category.assoc]
  rfl

/-- The explicit comparison from raw ordered Xi Hom to the chosen derived object. -/
def xiRawMappingComparison (C : Coefficient) [IsFibrant C] (x y : C.Obj) :
    (weakEquivalences SSet.{0}).Q.obj (JTOrderedFrameMate.XiOrdered C x y) ⟶
      orderedMappingObject C x y :=
  (weakEquivalences SSet.{0}).Q.map (xiRawToResolved C x y) ≫
    (xiLocalizationIso C x y).hom

/-- The explicit comparison from raw ordered Gamma Hom to the chosen derived object. -/
def gammaRawMappingComparison (C : Coefficient) [IsFibrant C] (x y : C.Obj) :
    (weakEquivalences SSet.{0}).Q.obj (JTOrderedFrameMate.GammaOrdered C x y) ⟶
      orderedMappingObject C x y :=
  (weakEquivalences SSet.{0}).Q.map (gammaRawToResolved C x y) ≫
    (gammaLocalizationIso C x y).hom

/-- The localized raw original ordered mate commutes with the specified
comparisons to the common chosen derived mapping object. This equation
asserts no invertibility of either raw comparison. -/
theorem rawOrderedMate_calibration (C : Coefficient) [IsFibrant C] (x y : C.Obj) :
    (weakEquivalences SSet.{0}).Q.map (JTOrderedFrameMate.orderedMate C x y) ≫
        gammaRawMappingComparison C x y = xiRawMappingComparison C x y := by
  have h := congrArg ((weakEquivalences SSet.{0}).Q.map)
    (orderedMate_resolution_square C x y)
  simp only [Functor.map_comp] at h
  change (weakEquivalences SSet.{0}).Q.map (JTOrderedFrameMate.orderedMate C x y) ≫
      ((weakEquivalences SSet.{0}).Q.map (gammaRawToResolved C x y) ≫
        (gammaLocalizationIso C x y).hom) = _
  rw [← Category.assoc, h, Category.assoc]
  change (weakEquivalences SSet.{0}).Q.map (xiRawToResolved C x y) ≫
      (resolvedOrderedMate C x y ≫ (gammaLocalizationIso C x y).hom) = _
  rw [resolvedOrderedMate_calibration]
  rfl

end

end DaggerModels.PartII.JTDerivedOrderedMate
