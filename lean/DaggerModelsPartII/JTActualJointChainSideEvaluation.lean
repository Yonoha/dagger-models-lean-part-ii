import DaggerModelsPartII.JTGraphCoveredLabelEvaluation
import DaggerModelsPartII.JTGraphCoveredPresentationWeak
import DaggerModelsPartII.JTActualJointChainSideGraph
import DaggerModelsPartII.JTActualJointChainSideRaw

/-! Reduced covered cylinders of the corrected side diagrams, including point targets. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

open CategoryTheory Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTActualJointChainSideEvaluation

open JTParametrizedTargetFamilies (Family codes)
open JTTargetJointMarks (Joint)
open JTActualJointChoiceChainGraph (Index base)
open JTActualJointChainSideLabels (leftLabels rightLabels)
open JTActualJointChainSideGraph (leftCodes rightCodes oldTime leftNative rightNative
  leftProjection rightProjection leftOver rightOver)
open JTActualJointMarkedEvaluation (left right)
open JTProjectiveOrderedFiberComparison (row)
open JTNecklaceEndpointCylinder (endpointInclusion)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code)

private abbrev marked (p : Index F j) :=
  (JTActualJointChoiceCover.projection F j).obj ((base F j).obj p)
private abbrev old (p : Index F j) := (marked F j p).1
private abbrev v (p : Index F j) := (marked F j p).2.val
private abbrev T (p : Index F j) := (codes L).obj (old F j p)

/-- Collapse the entire endpoint preimage in the corrected left graph. -/
abbrev leftReduced := JTGraphCoveredLabelEvaluation.reduced (left Q j)
  (leftLabels F j) (oldTime F j) (leftNative F j) (leftProjection F j)

/-- Collapse the full endpoint preimage in the corrected right graph. -/
abbrev rightReduced := JTGraphCoveredLabelEvaluation.reduced (right Q j)
  (rightLabels F j) (oldTime F j) (rightNative F j) (rightProjection F j)

/-- Recover the actual corrected native left cylinder with its original time. -/
abbrev leftToNative : leftReduced F j ⟶
    JTDecoratedIntervalCylinder.reduced (left Q j) (leftOver F j) (oldTime F j) :=
  JTGraphCoveredLabelEvaluation.projection (left Q j) (leftLabels F j)
    (oldTime F j) (leftNative F j) (leftProjection F j)

/-- Recover the actual corrected native right cylinder with its original time. -/
abbrev rightToNative : rightReduced F j ⟶
    JTDecoratedIntervalCylinder.reduced (right Q j) (rightOver F j) (oldTime F j) :=
  JTGraphCoveredLabelEvaluation.projection (right Q j) (rightLabels F j)
    (oldTime F j) (rightNative F j) (rightProjection F j)

/-- The added ending edge makes the source boundary monic even for a point side target. -/
theorem left_source_boundary_mono (p : Index F j) :
    Mono (endpointInclusion ((leftCodes F j).obj p)) := by
  apply NecklaceCylinderAugmentation.endpointInclusion_mono_of_pos
  change 0 < (cutLeft (T F j p) (v F j p)).len + 1
  omega

/-- The added starting edge likewise keeps the right source boundary monic. -/
theorem right_source_boundary_mono (p : Index F j) :
    Mono (endpointInclusion ((rightCodes F j).obj p)) := by
  apply NecklaceCylinderAugmentation.endpointInclusion_mono_of_pos
  change 0 < 1 + (cutRight (T F j p) (v F j p)).len
  omega

/-- The reduced left projection is weak for every actual cut, including endpoint cuts. -/
theorem leftToNative_weak (p : Index F j) :
    WeakEquivalence ((leftToNative F j).app p).right := by
  haveI := left_source_boundary_mono F j p
  exact JTGraphCoveredLabelEvaluation.projection_weak_of_native_mono (left Q j)
    (leftLabels F j) (oldTime F j) (leftNative F j) (leftProjection F j) p
    (JTActualJointChainSideGraph.leftProjection_trivialFibration F j p)

/-- The reduced right projection is weak with no restriction on the side target length. -/
theorem rightToNative_weak (p : Index F j) :
    WeakEquivalence ((rightToNative F j).app p).right := by
  haveI := right_source_boundary_mono F j p
  exact JTGraphCoveredLabelEvaluation.projection_weak_of_native_mono (right Q j)
    (rightLabels F j) (oldTime F j) (rightNative F j) (rightProjection F j) p
    (JTActualJointChainSideGraph.rightProjection_trivialFibration F j p)

/-- Forget the full left internal necklace, coefficient lift, and higher
choice, retaining precisely the original exactly transported source cut. -/
abbrev leftToMarked : BoundaryNecklaceComma.Presentation (leftReduced F j) ⥤
    JTExactlyMarkedSourceDiagram.Index F j :=
  Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram (leftReduced F j)) ⋙
    base F j ⋙ JTActualJointChoiceCover.projection F j

/-- The right covered presentation retains the same exact original source cut. -/
abbrev rightToMarked : BoundaryNecklaceComma.Presentation (rightReduced F j) ⥤
    JTExactlyMarkedSourceDiagram.Index F j :=
  Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram (rightReduced F j)) ⋙
    base F j ⋙ JTActualJointChoiceCover.projection F j

/-- The whole left internal-necklace presentation is a weak cover of the
exactly marked diagram, with every higher choice and original time retained. -/
theorem leftToMarked_weak
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence (nerveMap (leftToMarked F j)) := by
  let P := Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram (leftReduced F j))
  haveI : WeakEquivalence (nerveMap P) :=
    JTGraphCoveredPresentationWeak.forget_weak (left Q j) (leftLabels F j)
      (oldTime F j) (leftNative F j) (leftProjection F j)
      (JTActualJointChainSideGraph.leftProjection_trivialFibration F j)
  haveI := JTActualJointChoiceChainGraph.base_weak F j
  haveI := JTActualJointChoiceCover.projection_weak F j hW
  change WeakEquivalence (nerveMap P ≫ nerveMap (base F j) ≫
    nerveMap (JTActualJointChoiceCover.projection F j))
  infer_instance

/-- The same full weak-cover statement for the actual corrected right side. -/
theorem rightToMarked_weak
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence (nerveMap (rightToMarked F j)) := by
  let P := Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram (rightReduced F j))
  haveI : WeakEquivalence (nerveMap P) :=
    JTGraphCoveredPresentationWeak.forget_weak (right Q j) (rightLabels F j)
      (oldTime F j) (rightNative F j) (rightProjection F j)
      (JTActualJointChainSideGraph.rightProjection_trivialFibration F j)
  haveI := JTActualJointChoiceChainGraph.base_weak F j
  haveI := JTActualJointChoiceCover.projection_weak F j hW
  change WeakEquivalence (nerveMap P ≫ nerveMap (base F j) ≫
    nerveMap (JTActualJointChoiceCover.projection F j))
  infer_instance

/-- Evaluate every internal necklace of the corrected left diagram in the
literal fixed left target, with all higher choices and lifted coefficients. -/
def leftEvaluation : BoundaryNecklaceComma.Presentation (leftReduced F j) ⥤
    JTGraphFactoredPresentation.TargetComma (left Q j) :=
  JTGraphCoveredLabelEvaluation.evaluation (left Q j) (leftLabels F j)
    (oldTime F j) (leftNative F j) (leftProjection F j)
    (JTActualJointChainSideGraph.leftParameter F j) (by
      intro p
      let C := JTActualJointChainSideLabels.leftCoefficients F j p
      change lift (((leftProjection F j).app p) ≫
          fst ((leftCodes F j).obj p).toSSet
            (GroupoidSimplex.parameter.obj ((oldTime F j).obj p)))
          ((JTActualJointChainSideGraph.leftParameter F j).app p) ≫
        JTNecklaceLabelRealization.realizedLabel ((leftCodes F j).obj p).toSSet W
          ((JTActualJointChoiceChainGraph.ordinals F j).obj p)
          (JTRealizedLabelEndpoints.orderedLabel W x
            (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)
            (wedge (cutLeft (T F j p) (v F j p)) (single 1))
            ((JTActualJointChoiceChainGraph.ordinals F j).obj p)
            (JTComposedPrismLabels.orderedPoint C)) = _
      rw [JTComposedPrismLabels.orderedPoint_coefficient]
      exact JTActualJointChainSideRaw.left_raw F j p)

/-- The full corrected right evaluation uses the unchanged literal right target. -/
def rightEvaluation : BoundaryNecklaceComma.Presentation (rightReduced F j) ⥤
    JTGraphFactoredPresentation.TargetComma (right Q j) :=
  JTGraphCoveredLabelEvaluation.evaluation (right Q j) (rightLabels F j)
    (oldTime F j) (rightNative F j) (rightProjection F j)
    (JTActualJointChainSideGraph.rightParameter F j) (by
      intro p
      let C := JTActualJointChainSideLabels.rightCoefficients F j p
      change lift (((rightProjection F j).app p) ≫
          fst ((rightCodes F j).obj p).toSSet
            (GroupoidSimplex.parameter.obj ((oldTime F j).obj p)))
          ((JTActualJointChainSideGraph.rightParameter F j).app p) ≫
        JTNecklaceLabelRealization.realizedLabel ((rightCodes F j).obj p).toSSet W
          ((JTActualJointChoiceChainGraph.ordinals F j).obj p)
          (JTRealizedLabelEndpoints.orderedLabel W
            (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j) y
            (wedge (single 1) (cutRight (T F j p) (v F j p)))
            ((JTActualJointChoiceChainGraph.ordinals F j).obj p)
            (JTComposedPrismLabels.orderedPoint C)) = _
      rw [JTComposedPrismLabels.orderedPoint_coefficient]
      exact JTActualJointChainSideRaw.right_raw F j p)

end
end DaggerModels.PartII.JTActualJointChainSideEvaluation
