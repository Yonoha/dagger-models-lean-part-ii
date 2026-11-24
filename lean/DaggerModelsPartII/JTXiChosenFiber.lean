import DaggerModelsPartII.JTXiRowEndpoints
import DaggerModelsPartII.JTXiDerivedMapping
import DaggerModelsPartII.JTActualDerivedOrderedMate
import DaggerModelsPartII.JTRightEndpointCartesian
import DaggerModelsPartII.JTOrdinaryEndpointFibration

/-!
# The original Xi chosen endpoint fiber

The raw original endpoint arrow is retained. The comparison from its strict
fiber is the actual factorization-unit inclusion at the unchanged ordered
point. Its localization is normalized to the same chosen derived mapping
object and to the retained original ordered mate on the Gamma side.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Simplicial DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTXiChosenFiber

open JTRelativeReedyFrame JTXiRowEndpoints

noncomputable section

private local instance : HasLimits Coefficient := daggerSimplicialCatHasLimits
private local instance : HasColimits Coefficient := daggerSimplicialCatHasColimits
private local instance : ModelCategory Coefficient :=
  DaggerActualRigidificationQuillen.modelG.{0}

/-- The original dagger endpoint arrow is a Kan fibration whenever its
underlying target is a quasi-category. The model on this mapping arrow is
Kan; the ordinary coefficient-model argument is in the imported theorem. -/
theorem daggerEndpointArrow_fibration (X : DaggerSSet.{0})
    [X.toSSet.Quasicategory] :
    Fibration (JTRightAdjointOrderedFiber.daggerEndpointArrow X) := by
  haveI : Fibration (JTRightAdjointOrderedFiber.ordinaryEndpointArrow X.toSSet) :=
    JTOrdinaryEndpointFibration.ordinaryEndpointArrow_fibration X.toSSet
  apply (fibration_iff _).mpr
  exact (fibrations SSet.{0}).of_isPullback
    (JTRightEndpointCartesian.endpoint_isPullback X) ((fibration_iff _).mp inferInstance)

/-- The raw Xi categorical endpoint arrow is a Kan fibration for every
coefficient fibrant in the original dagger Bergner model. -/
theorem xiEndpointArrow_fibration (C : Coefficient) [IsFibrant C] :
    Fibration (xiEndpointArrow C) := by
  let X := OrdinaryRigidification.DaggerNerve.daggerCoherentNerve.obj C
  have hKan :=
    (DaggerActualFibrantCounitReduction.fibrant_iff_localKan C).1 inferInstance
  letI : X.toSSet.Quasicategory :=
    DaggerOrdinaryRigidificationCof.OriginalNerveQuasicategory.coherentNerve_quasicategory
      C.toSimplicialCat hKan
  change Fibration (JTRightAdjointOrderedFiber.daggerEndpointArrow X)
  exact daggerEndpointArrow_fibration X

/-- The chosen homotopy fiber of the literal original Xi endpoint arrow at
its original specified ordered point. -/
def xiHomotopyFiber (C : Coefficient) (x y : C.Obj) : SSet.{0} :=
  ChosenHomotopyFiberComparison.chosenFiber (xiEndpointArrow C) (boundaryPoint C x y)

/-- The canonical strict-to-chosen-fiber map, preceded only by the checked
original Xi strict-fiber presentation. -/
def xiInclusion (C : Coefficient) (x y : C.Obj) :
    JTOrderedFrameMate.XiOrdered C x y ⟶ xiHomotopyFiber C x y :=
  (xiStrictFiberIso C x y).hom ≫
    ChosenHomotopyFiberTriangle.inclusion (xiEndpointArrow C) (boundaryPoint C x y)

/-- The specified canonical inclusion is Kan weak; no alternate map is
chosen using a localization isomorphism. -/
theorem xiInclusion_weak (C : Coefficient) [IsFibrant C] (x y : C.Obj) :
    WeakEquivalence (xiInclusion C x y) := by
  haveI : Fibration (xiEndpointArrow C) := xiEndpointArrow_fibration C
  haveI : WeakEquivalence
      (ChosenHomotopyFiberTriangle.inclusion (xiEndpointArrow C) (boundaryPoint C x y)) :=
    ChosenHomotopyFiberTriangle.inclusion_weak _ _
  change WeakEquivalence ((xiStrictFiberIso C x y).hom ≫ _)
  infer_instance

/-- Localization of the specified canonical strict-fiber inclusion. -/
def xiInclusionLocalizationIso (C : Coefficient) [IsFibrant C] (x y : C.Obj) :
    (weakEquivalences SSet.{0}).Q.obj (JTOrderedFrameMate.XiOrdered C x y) ≅
      (weakEquivalences SSet.{0}).Q.obj (xiHomotopyFiber C x y) :=
  Localization.isoOfHom (weakEquivalences SSet.{0}).Q (weakEquivalences SSet.{0})
    (xiInclusion C x y) ((weakEquivalence_iff _).mp (xiInclusion_weak C x y))

/-- The actual original Xi chosen fiber represents the retained derived
mapping object, with normalization through the specified inclusion. -/
def xiFiberLocalizationIso (C : Coefficient) [IsFibrant C] (x y : C.Obj) :
    (weakEquivalences SSet.{0}).Q.obj (xiHomotopyFiber C x y) ≅
      JTDerivedOrderedMate.orderedMappingObject C x y :=
  (xiInclusionLocalizationIso C x y).symm ≪≫ JTXiDerivedMapping.xiRawMappingIso C x y

/-- The chosen Xi fiber normalization extends the retained original raw
mapping comparison along the actual canonical weak inclusion. -/
theorem xiFiberLocalization_calibration (C : Coefficient) [IsFibrant C]
    (x y : C.Obj) :
    (weakEquivalences SSet.{0}).Q.map (xiInclusion C x y) ≫
        (xiFiberLocalizationIso C x y).hom =
      (JTXiDerivedMapping.xiRawMappingIso C x y).hom := by
  change (xiInclusionLocalizationIso C x y).hom ≫
    ((xiInclusionLocalizationIso C x y).inv ≫ _) = _
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The retained actual ordered mate, interpreted on the two original
chosen endpoint homotopy fibers through the actual weak Xi inclusion. -/
def actualChosenDerivedMateIso (C : Coefficient) [IsFibrant C] (x y : C.Obj) :
    (weakEquivalences SSet.{0}).Q.obj (xiHomotopyFiber C x y) ≅
      (weakEquivalences SSet.{0}).Q.obj (JTGammaDerivedFiber.gammaHomotopyFiber C x y) :=
  (xiInclusionLocalizationIso C x y).symm ≪≫
    JTActualDerivedOrderedMate.actualDerivedOrderedMateIso C x y

/-- Composing with the specified Xi inclusion recovers exactly the
retained actual mate-to-Gamma-fiber map after localization. -/
theorem actualChosenDerivedMate_inclusion (C : Coefficient) [IsFibrant C]
    (x y : C.Obj) :
    (weakEquivalences SSet.{0}).Q.map (xiInclusion C x y) ≫
        (actualChosenDerivedMateIso C x y).hom =
      (weakEquivalences SSet.{0}).Q.map
        (JTActualDerivedOrderedMate.actualToGammaFiber C x y) := by
  change (xiInclusionLocalizationIso C x y).hom ≫
    ((xiInclusionLocalizationIso C x y).inv ≫ _) = _
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rfl

/-- Both actual chosen-fiber normalizations agree on the specified
localized original ordered mate. -/
theorem actualChosenDerivedMate_calibration (C : Coefficient) [IsFibrant C]
    (x y : C.Obj) :
    (actualChosenDerivedMateIso C x y).hom ≫
        (JTGammaDerivedFiber.gammaFiberLocalizationIso C x y).hom =
      (xiFiberLocalizationIso C x y).hom := by
  change ((xiInclusionLocalizationIso C x y).inv ≫
    (JTActualDerivedOrderedMate.actualDerivedOrderedMateIso C x y).hom) ≫ _ = _
  rw [Category.assoc, JTActualDerivedOrderedMate.actualDerivedOrderedMate_calibration]
  rfl

end

end DaggerModels.PartII.JTXiChosenFiber
