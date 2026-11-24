import DaggerModelsPartII.JTGraphCoveredLabelEvaluation

/-! The actual higher-choice chain cylinder in the original fixed target. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open HomotopicalAlgebra DaggerModels DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTActualJointChainCylinder

open JTParametrizedTargetFamilies (Family)
open JTTargetJointMarks (Joint)
open JTActualJointChoiceChainGraph (Index)
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time) (j : Joint Q.code)

private abbrev labels := JTActualJointChainLabels.chainLabels F j
private abbrev oldTime :=
  JTActualJointChoiceChainGraph.base F j ⋙
    JTActualJointChoiceCover.projection F j ⋙
      JTExactlyMarkedSourceDiagram.base F j ⋙ time
private abbrev collapse := (JTActualJointChoiceChainGraph.original F j).collapse
private abbrev graph := JTActualJointChoiceChainGraph.graphCover F j
private abbrev π := JTActualJointChoiceChainGraph.graphProjection F j
private abbrev θ := JTActualJointChainLabels.chainParameter F j

/-- Collapse every point in the inverse image of the actual endpoint boundary. -/
abbrev reduced :=
  JTGraphCoveredLabelEvaluation.reduced Q (labels F j) (oldTime F j)
    (collapse F j) (π F j)

/-- Recover the original reduced native cylinder. -/
abbrev projection : reduced F j ⟶
    JTDecoratedIntervalCylinder.reduced Q
      (JTJointRelativeGraphFamily.native (JTActualJointChoiceChainGraph.original F j))
      (oldTime F j) :=
  JTGraphCoveredLabelEvaluation.projection Q (labels F j) (oldTime F j)
    (collapse F j) (π F j)

/-- Positive target length makes each reduced projection weak. -/
theorem projection_weak (hQ : 0 < Q.code.len) (p : Index F j) :
    WeakEquivalence ((projection F j).app p).right :=
  JTGraphCoveredLabelEvaluation.projection_weak Q (labels F j) (oldTime F j)
    (collapse F j) (π F j) hQ p
      (JTActualJointChoiceChainGraph.graphProjection_trivialFibration F j p)

/-- Evaluate all internal necklaces in the unchanged fixed-target comma. -/
abbrev evaluation :
    BoundaryNecklaceComma.Presentation (reduced F j) ⥤
      JTGraphFactoredPresentation.TargetComma Q :=
  JTGraphCoveredLabelEvaluation.evaluation Q (labels F j) (oldTime F j)
    (collapse F j) (π F j) (θ F j) (JTActualJointChainLabels.raw F j)

end
end DaggerModels.PartII.JTActualJointChainCylinder

