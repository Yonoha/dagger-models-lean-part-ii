import DaggerModelsPartII.JTDerivedOrderedAction
import DaggerModelsPartII.EndpointMappingFiber
import DaggerModelsPartII.ChosenHomotopyFiberComparison
import DaggerModelsPartII.JTGammaRowEndpoints

/-!
# The actual Gamma ordered homotopy fiber and the chosen endpoint frame

The literal qG replacement supplies a weak square of endpoint mapping arrows
whose resolved arrow is a Kan fibration. The strict ordered fiber of that
resolved arrow is the Hom simplicial set under the original boundary from
QGFrame. The comparison below therefore computes the chosen homotopy fiber
of the original Gamma endpoint mapping arrow, without inverting its raw
strict-fiber comparison.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Simplicial DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTGammaDerivedFiber

open JTRelativeReedyFrame JTEndpointArrowReplacement JTEndpointAugmentations
open JTEndpointCobaseAugmentations JTDerivedOrderedAction JTEndpointFrames
open JTActualCosimplicialFrame

noncomputable section

private local instance : HasLimits Coefficient := daggerSimplicialCatHasLimits
private local instance : HasColimits Coefficient := daggerSimplicialCatHasColimits
private local instance : ModelCategory Coefficient :=
  DaggerActualRigidificationQuillen.modelG.{0}

/-- The actual original Gamma endpoint mapping arrow. -/
def rawArrow (C : Coefficient) :=
  JTGammaRowEndpoints.gammaEndpointArrow C

/-- The endpoint mapping arrow from the literal zero-fixed qG replacement. -/
def resolvedArrow (C : Coefficient) :=
  EndpointMappingFiber.precomp (Z := C) (structureMap QG)

/-- The original specified ordered endpoint point. -/
def rawPoint (C : Coefficient) (x y : C.Obj) :=
  EndpointMappingFiber.endpointPoint (sourceAug (arrowAugmentation augmentation))
    (JTEndpointHom.boundaryTarget C x y)

/-- The arrow-augmentation point is the actual original nerve-row boundary point. -/
theorem rawPoint_eq_boundaryPoint (C : Coefficient) (x y : C.Obj) :
    rawPoint C x y = JTGammaRowEndpoints.boundaryPoint C x y := rfl

/-- Its actual image under the qG source component. -/
def resolvedPoint (C : Coefficient) (x y : C.Obj) :=
  EndpointMappingFiber.endpointPoint (sourceAug QGaugmentation)
    (JTEndpointHom.boundaryTarget C x y)

private def totalComparison (C : Coefficient) :=
  (JTGammaRowEndpoints.gammaRowMappingIso C JTOrderedFrameMate.oneIndex).hom ≫
    (StrictFrameMappingWeak.strictMapping C).map qGammaTarget

private def baseComparison (C : Coefficient) :=
  (StrictFrameMappingWeak.strictMapping C).map qGammaSource

private theorem mapping_square (C : Coefficient) :
    rawArrow C ≫ baseComparison C = totalComparison C ≫ resolvedArrow C := by
  simpa only [rawArrow, JTGammaRowEndpoints.gammaEndpointArrow, totalComparison,
    Category.assoc] using congrArg
      (fun t ↦ (JTGammaRowEndpoints.gammaRowMappingIso C JTOrderedFrameMate.oneIndex).hom ≫ t)
        (gamma_mapping_square C)

/-- The augmentation identity retains both endpoints in their original order. -/
theorem endpoint_point_square (C : Coefficient) (x y : C.Obj) :
    rawPoint C x y ≫ baseComparison C = resolvedPoint C x y := by
  exact EndpointMappingFiber.endpointPoint_precomp
    (sourceAug (arrowAugmentation augmentation)) (JTEndpointHom.boundaryTarget C x y)
    (Functor.whiskerRight qG Arrow.leftFunc) (sourceAug QGaugmentation) rfl

/-- The exact chosen homotopy fiber of the original Gamma endpoint arrow. -/
def gammaHomotopyFiber (C : Coefficient) (x y : C.Obj) : SSet.{0} :=
  ChosenHomotopyFiberComparison.chosenFiber (rawArrow C) (rawPoint C x y)

/-- The actual resolved strict fiber is the original under-boundary QG Hom. -/
def resolvedFiberIso (C : Coefficient) (x y : C.Obj) :
    JTEndpointFrameComparison.homSSet QGFrame C x y ≅
      pullback (resolvedArrow C) (resolvedPoint C x y) :=
  EndpointMappingFiber.underFiberIso (structureMap QG) (sourceAug QGaugmentation)
    (JTEndpointHom.boundaryTarget C x y)

/-- The comparison uses the actual raw square and its actual endpoint point. -/
def gammaFiberComparison (C : Coefficient) [IsFibrant C] (x y : C.Obj) :
    gammaHomotopyFiber C x y ⟶ JTEndpointFrameComparison.homSSet QGFrame C x y := by
  haveI : Fibration (resolvedArrow C) := qGamma_mapping_fibration C
  exact ChosenHomotopyFiberComparison.comparison (rawArrow C) (resolvedArrow C)
    (totalComparison C) (baseComparison C) (mapping_square C)
    (rawPoint C x y) (resolvedPoint C x y) (endpoint_point_square C x y) ≫
      (resolvedFiberIso C x y).inv

/-- The chosen QG endpoint frame represents the original Gamma homotopy
fiber over the specified actual ordered endpoints. -/
theorem gammaFiberComparison_weak (C : Coefficient) [IsFibrant C] (x y : C.Obj) :
    WeakEquivalence (gammaFiberComparison C x y) := by
  haveI : Fibration (resolvedArrow C) := qGamma_mapping_fibration C
  haveI : WeakEquivalence
      ((StrictFrameMappingWeak.strictMapping C).map qGammaTarget) :=
    (weakEquivalence_iff _).mpr (gamma_target_mapping_weak C)
  haveI : WeakEquivalence (totalComparison C) := by
    dsimp only [totalComparison]
    infer_instance
  haveI : WeakEquivalence (baseComparison C) :=
    (weakEquivalence_iff _).mpr (gamma_source_mapping_weak C)
  haveI : WeakEquivalence
      (ChosenHomotopyFiberComparison.comparison (rawArrow C) (resolvedArrow C)
        (totalComparison C) (baseComparison C) (mapping_square C)
        (rawPoint C x y) (resolvedPoint C x y) (endpoint_point_square C x y)) :=
    ChosenHomotopyFiberComparison.comparison_weak (rawArrow C) (resolvedArrow C)
      (totalComparison C) (baseComparison C) (mapping_square C)
      (rawPoint C x y) (resolvedPoint C x y) (endpoint_point_square C x y)
  change WeakEquivalence (_ ≫ (resolvedFiberIso C x y).inv)
  infer_instance

/-- The original Gamma ordered homotopy fiber computes the same chosen
derived mapping object from the original interval under its two endpoints. -/
def gammaFiberLocalizationIso (C : Coefficient) [IsFibrant C] (x y : C.Obj) :
    (weakEquivalences SSet.{0}).Q.obj (gammaHomotopyFiber C x y) ≅
      JTDerivedOrderedMate.orderedMappingObject C x y :=
  Localization.isoOfHom (weakEquivalences SSet.{0}).Q (weakEquivalences SSet.{0})
    (gammaFiberComparison C x y)
    ((weakEquivalence_iff _).mp (gammaFiberComparison_weak C x y)) ≪≫
      JTDerivedOrderedMate.gammaLocalizationIso C x y

/-- The chosen localization isomorphism retains the specified actual
Gamma-fiber comparison and the retained frame normalization. -/
theorem gammaFiberLocalizationIso_hom (C : Coefficient) [IsFibrant C] (x y : C.Obj) :
    (gammaFiberLocalizationIso C x y).hom =
      (weakEquivalences SSet.{0}).Q.map (gammaFiberComparison C x y) ≫
        (JTDerivedOrderedMate.gammaLocalizationIso C x y).hom := rfl

end

end DaggerModels.PartII.JTGammaDerivedFiber
