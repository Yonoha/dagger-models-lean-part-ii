import DaggerModelsPartII.JTRawCEEvaluatorTransport
import DaggerModelsPartII.JTOrderedCEEvaluator
import DaggerModelsPartII.JTInjectiveOrderedEndpointFibration
import DaggerModelsPartII.JTOrdinaryEndpointFibration

/-! Exact transfer of the original raw strict ordered-fiber action to its
chosen homotopy-fiber action, using the checked CE evaluator comparison. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTRawChosenFiberBridge

open JTRawCEEvaluatorTransport

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev CE :=
  Under.lift JTXiEndpointCollapse.CE JTXiEndpointCollapse.CE_boundary

private abbrev u (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :=
  (JTRawFreeInnerComparison.ell W).hom.app (op ⦋0⦌)
    (JTGtildeOrderedFiberAction.targetVertices W x y).1

private abbrev v (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :=
  (JTRawFreeInnerComparison.ell W).hom.app (op ⦋0⦌)
    (JTGtildeOrderedFiberAction.targetVertices W x y).2

/-- The exact raw strict-fiber map is weak from the original decorated
evaluator; CE evaluation and weights are discharged by their checked
quasi-category theorems. -/
theorem rawStrictFiberMapAtP_weak (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌))
    (hW : @IsFibrant Source _ SegalLocalizers.injectiveSegalModel.categoryWithFibrations _ W)
    (hDecorated : WeakEquivalence
      (DecoratedNecklaceHomBar.evaluator W
        (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
        (JTProjectiveOrderedFiberComparison.targetVertices W x y).2)) :
    WeakEquivalence (JTRawUnitCylinderCalibration.rawStrictFiberMapAtP W x y) := by
  letI : (JTRawFreeInnerComparison.rawTarget W).toSSet.Quasicategory :=
    JTFreeInnerFactorization.replacement_underlying_quasicategory
      (DaggerJTRealization.daggerRealization.obj W)
  have hCE : WeakEquivalence
      (JTOrderedFrameHomBar.evaluator CE (ceTarget W x y)) := by
    change WeakEquivalence (JTOrderedFrameHomBar.evaluator CE
      (JTConeMappingPresentation.targetUnder
        (JTRawFreeInnerComparison.rawTarget W).toSSet (u W x y) (v W x y)))
    exact JTOrderedCEEvaluator.evaluator_weak
      (JTRawFreeInnerComparison.rawTarget W).toSSet (u W x y) (v W x y)
  exact rawStrictFiberMapAtP_weak_of_evaluators W x y hW hDecorated hCE
    JTOrderedFrameWeights.ce_point_GW

/-- The original raw chosen-fiber map is weak for the same evaluator
premise, through the specified strict-to-chosen inclusion triangle. -/
theorem rawChosenFiberMapAtP_weak (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌))
    (hW : @IsFibrant Source _ SegalLocalizers.injectiveSegalModel.categoryWithFibrations _ W)
    (hDecorated : WeakEquivalence
      (DecoratedNecklaceHomBar.evaluator W
        (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
        (JTProjectiveOrderedFiberComparison.targetVertices W x y).2)) :
    WeakEquivalence (JTRawOrdinaryAdjoint.rawChosenFiberMapAtP W x y) := by
  have hKan : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ;
      IsFibrant W :=
    ((SegalLocalizers.injectiveSegalModel_isFibrant_iff W).mp hW).1
  letI : (JTRawFreeInnerComparison.rawTarget W).toSSet.Quasicategory :=
    JTFreeInnerFactorization.replacement_underlying_quasicategory
      (DaggerJTRealization.daggerRealization.obj W)
  letI : Fibration (JTProjectiveOrderedFiberComparison.endpointArrow W) :=
    JTInjectiveOrderedEndpointFibration.endpointArrow_fibration W hKan
  letI : Fibration
      (JTRightAdjointOrderedFiber.ordinaryEndpointArrow
        (JTRawFreeInnerComparison.rawTarget W).toSSet) :=
    JTOrdinaryEndpointFibration.ordinaryEndpointArrow_fibration
      (JTRawFreeInnerComparison.rawTarget W).toSSet
  letI : WeakEquivalence (JTRawUnitCylinderCalibration.rawStrictFiberMapAtP W x y) :=
    rawStrictFiberMapAtP_weak W x y hW hDecorated
  letI : WeakEquivalence
      (ChosenHomotopyFiberTriangle.inclusion
        (JTProjectiveOrderedFiberComparison.endpointArrow W)
        (JTProjectiveOrderedFiberComparison.point W
          (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
          (JTProjectiveOrderedFiberComparison.targetVertices W x y).2)) :=
    ChosenHomotopyFiberTriangle.inclusion_weak _ _
  letI : WeakEquivalence
      (ChosenHomotopyFiberTriangle.inclusion
        (JTRightAdjointOrderedFiber.ordinaryEndpointArrow
          (JTRawFreeInnerComparison.rawTarget W).toSSet)
        (JTRightAdjointOrderedFiber.ordinaryEndpointPoint
          (JTRawFreeInnerComparison.rawTarget W)
          (u W x y) (v W x y))) :=
    ChosenHomotopyFiberTriangle.inclusion_weak _ _
  have hTriangle := JTRawSingleOrderedLabelIso.rawChosenFiberMapAtP_inclusion W x y
  have hcomp : WeakEquivalence
      (ChosenHomotopyFiberTriangle.inclusion
          (JTProjectiveOrderedFiberComparison.endpointArrow W)
          (JTProjectiveOrderedFiberComparison.point W
            (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
            (JTProjectiveOrderedFiberComparison.targetVertices W x y).2) ≫
        JTRawOrdinaryAdjoint.rawChosenFiberMapAtP W x y) := by
    rw [hTriangle]
    infer_instance
  exact (weakEquivalence_precomp_iff _ _).mp hcomp

end

end DaggerModels.PartII.JTRawChosenFiberBridge
