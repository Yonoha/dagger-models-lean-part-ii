import DaggerModelsPartII.JTJointPairGapChainRaw
import DaggerModelsPartII.JTGraphCoveredLabelEvaluation
import DaggerModelsPartII.JTGraphCoveredPresentationWeak

/-! Every internal necklace of the full paired-cut graph evaluates at the literal joint. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

open CategoryTheory Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTJointPairGapChainEvaluation

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row)
open JTTargetJointMarks (Joint)
open JTJointPairGapChainLabels (labels native)
open JTJointPairGapChainParameter (oldTime)
open JTJointPairGapChainGraph (projection parameter)
open JTPointTargetEvaluationCone (pointTarget)
open JTParametrizedBeadGraph (jointCoefficient)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code)

private abbrev I := JTJointPairChainDiagram.Index F j
private abbrev z := jointCoefficient (Q := Q) j
private abbrev target := pointTarget W (z j)

/-- Collapse the whole padded native interval to the same literal joint. -/
abbrev collapse : codes (labels F j) ⟶ (Functor.const (I F j)).obj (target j).code :=
  JTOrderedLabelJointInsertion.toPointNatural (native F j)

private abbrev over := Over.lift (codes (labels F j)) (collapse F j)

/-- Collapse the full inverse image of both endpoint lines of the paired-cut graph. -/
abbrev reduced := JTGraphCoveredLabelEvaluation.reduced (target j) (labels F j)
  (oldTime F j) (collapse F j) (projection F j)

/-- Recover the complete native cylinder with its unchanged original time. -/
abbrev toNative : reduced F j ⟶
    JTDecoratedIntervalCylinder.reduced (target j) (over F j) (oldTime F j) :=
  JTGraphCoveredLabelEvaluation.projection (target j) (labels F j)
    (oldTime F j) (collapse F j) (projection F j)

/-- The two added edges make the source endpoint boundary monic, even at a point target. -/
theorem source_boundary_mono (p : I F j) :
    Mono (JTNecklaceEndpointCylinder.endpointInclusion ((codes (labels F j)).obj p)) := by
  apply NecklaceCylinderAugmentation.endpointInclusion_mono_of_pos
  change 0 < 1 + (_ + 1)
  omega

/-- Reduction retains a weak comparison with the original entire native cylinder. -/
theorem toNative_weak (p : I F j) : WeakEquivalence ((toNative F j).app p).right := by
  haveI := source_boundary_mono F j p
  exact JTGraphCoveredLabelEvaluation.projection_weak_of_native_mono (target j)
    (labels F j) (oldTime F j) (collapse F j) (projection F j) p
    (JTJointPairGapChainGraph.projection_trivialFibration F j p)

/-- The full internal-necklace presentation remembers exactly both original cuts. -/
abbrev toPairs : BoundaryNecklaceComma.Presentation (reduced F j) ⥤
    JTJointPairSourceDiagram.Index F j :=
  Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram (reduced F j)) ⋙
    JTJointPairChainDiagram.base F j ⋙ JTJointPairChoiceCover.projection F j

/-- This is a weak cover of the exact pair category, with all higher choices kept. -/
theorem toPairs_weak
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence (nerveMap (toPairs F j)) := by
  let P := Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram (reduced F j))
  haveI : WeakEquivalence (nerveMap P) :=
    JTGraphCoveredPresentationWeak.forget_weak (target j) (labels F j)
      (oldTime F j) (collapse F j) (projection F j)
      (JTJointPairGapChainGraph.projection_trivialFibration F j)
  haveI := JTJointPairChainDiagram.base_weak F j
  haveI := JTJointPairChoiceCover.projection_weak F j hW
  change WeakEquivalence (nerveMap P ≫ nerveMap (JTJointPairChainDiagram.base F j) ≫
    nerveMap (JTJointPairChoiceCover.projection F j))
  infer_instance

/-- Evaluate all internal necklaces of the full graph in the point-target comma.
A cone to the point LABEL does not follow from this raw equality alone. -/
def evaluation : BoundaryNecklaceComma.Presentation (reduced F j) ⥤
    JTGraphFactoredPresentation.TargetComma (target j) :=
  JTGraphCoveredLabelEvaluation.evaluation (target j) (labels F j)
    (oldTime F j) (collapse F j) (projection F j) (parameter F j) (by
      intro p
      let C := JTJointPairGapChainLabels.coefficients F j p
      let T := JTJointPairGapChainLabels.code F j p
      change lift (((projection F j).app p) ≫ fst T.toSSet
          (J.obj ((oldTime F j).obj p))) ((parameter F j).app p) ≫
        JTNecklaceLabelRealization.realizedLabel T.toSSet W
          ((JTJointPairChainDiagram.ordinals F j).obj p)
          (JTRealizedLabelEndpoints.orderedLabel W (z j) (z j) T
            ((JTJointPairChainDiagram.ordinals F j).obj p)
            (JTComposedPrismLabels.orderedPoint C)) = _
      rw [JTComposedPrismLabels.orderedPoint_coefficient]
      have ht : (JTOrderedLabelJointInsertion.toPoint T).map = term T.toSSet :=
        JTOrderedLabelJointInsertion.pointIsTerminal.hom_ext _ _
      change _ = (((projection F j).app p) ≫ fst T.toSSet
        (J.obj ((oldTime F j).obj p))) ≫
          (JTOrderedLabelJointInsertion.toPoint T).map ≫ (target j).map
      rw [ht]
      exact JTJointPairGapChainRaw.raw F j p)

end
end DaggerModels.PartII.JTJointPairGapChainEvaluation
