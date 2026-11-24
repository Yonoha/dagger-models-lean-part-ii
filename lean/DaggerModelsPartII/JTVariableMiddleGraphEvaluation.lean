import DaggerModelsPartII.JTWhiskeredGraphRaw
import DaggerModelsPartII.JTVariableMiddleWhiskeredDiagram
import DaggerModelsPartII.JTGraphCoveredPresentationWeak

/-! Complete graph evaluations with varying left, middle and right native necklaces. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTVariableMiddleGraphEvaluation

open JTParametrizedTargetFamilies (codes)
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter

variable {I : Type} [SmallCategory I] {W : Source} {x y : Vertex W}
variable {P M R : I ⥤ NecklaceCode} {K : I ⥤ SimplexCategory}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (F : JTVariableMiddleWhiskeredDiagram.Family (W := W) (x := x) (y := y) P M R K)
variable (time : I ⥤ SimplexCategory)
variable (c : codes F.labels ⟶ (Functor.const I).obj Q.code)

/-- The whole original native-time product, with its specified collapse to Q. -/
abbrev productDiagram : I ⥤ SSet.{0} :=
  JTJointRelativeParameters.withTime Q.map J time (Over.lift (codes F.labels) c)
    (JTTargetIntervalOverMapping.whole Q.code)

variable {Y : I ⥤ SSet.{0}} (π : Y ⟶ productDiagram Q F time c)
variable (θ : Y ⟶ JTParametrizedTargetFamilyComparison.degrees F.labels ⋙ J)

/-- Keep the actual whole native coordinate of every graph point. -/
abbrev nativeCoordinate (a : I) :
    Y.obj a ⟶ (wedge (P.obj a) (wedge (M.obj a) (R.obj a))).toSSet :=
  π.app a ≫ fst ((codes F.labels).obj a).toSSet (J.obj (time.obj a))

/-- The fixed raw target is the ORIGINAL collapse followed by the map of Q. -/
abbrev rawTarget (a : I) :
    (wedge (P.obj a) (wedge (M.obj a) (R.obj a))).toSSet ⟶ Raw W :=
  (c.app a).map ≫ Q.map

variable (H : ∀ a : I, JTWhiskeredGraphRaw.PieceEquations W (F.data a)
  (nativeCoordinate Q F time c π a) (θ.app a) (rawTarget Q F c a))

include H in
/-- The three exact covered piece equations give the whole decorated raw
equation required by the existing fixed-target evaluation construction. -/
theorem raw (a : I) :
    lift (π.app a ≫ fst ((codes F.labels).obj a).toSSet (J.obj (time.obj a)))
        (θ.app a) ≫
      JTNecklaceLabelRealization.realizedLabel ((codes F.labels).obj a).toSSet W
        ((JTParametrizedTargetFamilyComparison.degrees F.labels).obj a)
        (JTRealizedLabelEndpoints.orderedLabel W x y ((codes F.labels).obj a)
          ((JTParametrizedTargetFamilyComparison.degrees F.labels).obj a)
          (OrderedLabelElements.label W (OrderedNecklaceVertexPoints.boundaryPoint W x y)
            (F.labels.obj a))) =
    (π.app a ≫ fst ((codes F.labels).obj a).toSSet (J.obj (time.obj a))) ≫
      ((Over.lift (codes F.labels) c).obj a).hom.map ≫ Q.map :=
  JTWhiskeredGraphRaw.PieceEquations.ordered_raw W (F.data a) (H a)

/-- Collapse the full inverse image of BOTH original endpoint lines. -/
abbrev reduced : I ⥤ Under JTXiEndpointCollapse.boundary :=
  JTGraphCoveredLabelEvaluation.reduced Q F.labels time c π

/-- The entire graph-covered diagram lifts to the literal original pullback
diagram, before any internal necklace is chosen. -/
def pullbackLift : reduced Q F time c π ⟶ F.labels ⋙ JTTargetCommaPullback.diagram W x y Q :=
  JTDecoratedIntervalCylinder.liftFromProjections Q F.labels (reduced Q F time c π)
    (JTGraphCoveredLabelEvaluation.decorated Q F.labels time c π θ)
    (JTGraphCoveredLabelEvaluation.nativeLeg Q F.labels time c π)
    (JTGraphCoveredLabelEvaluation.raw_square Q F.labels time c π θ
      (raw Q F time c π θ H))

/-- Evaluate ALL internal necklaces in the unchanged original TargetComma Q.
Only the exact piece equations are inputs, not a presumed whole raw equation. -/
def evaluation : BoundaryNecklaceComma.Presentation (reduced Q F time c π) ⥤
    JTGraphFactoredPresentation.TargetComma Q :=
  JTGraphCoveredLabelEvaluation.evaluation Q F.labels time c π θ (raw Q F time c π θ H)

/-- This is exactly the full pullback-presentation evaluation, so later
decorated comparisons can use the existing presentation transport machinery. -/
theorem evaluation_eq_mapPresentation : evaluation Q F time c π θ H =
    JTBoundaryNecklacePresentationCone.mapPresentation (JTTargetCommaPullback.diagram W x y Q)
      (reduced Q F time c π) F.labels (pullbackLift Q F time c π θ H) ⋙
        JTTargetCommaExactEvaluation.fromPresentation W x y Q := rfl

/-- Project the complete internal-necklace presentation to its original index. -/
abbrev toOriginal : BoundaryNecklaceComma.Presentation (reduced Q F time c π) ⥤ I :=
  Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram (reduced Q F time c π))

/-- A componentwise trivial-fibration graph gives a weak presentation cover,
for every target length and without a contractibility assumption on I. -/
theorem toOriginal_weak (hπ : ∀ a : I, trivialFibrations SSet.{0} (π.app a)) :
    WeakEquivalence (nerveMap (toOriginal Q F time c π)) :=
  JTGraphCoveredPresentationWeak.forget_weak Q F.labels time c π hπ

end

end DaggerModels.PartII.JTVariableMiddleGraphEvaluation
