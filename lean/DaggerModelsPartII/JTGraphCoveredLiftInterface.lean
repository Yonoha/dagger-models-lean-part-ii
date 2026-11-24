import DaggerModelsPartII.JTGraphCoveredLabelEvaluation
import DaggerModelsPartII.JTBoundaryNecklaceTwoReindexComparison

/-!
A generic fixed-target lift interface for full graph-covered evaluations.
The existing evaluator is exactly its map on complete presentations followed
by the original comma evaluation. Expose this before concrete choice families
are substituted, so no new source, raw equation or target is introduced.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphCoveredLiftInterface

open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTParametrizedTargetFamilies (codes)
open JTTargetIntervalOverMapping (whole)
open DecoratedCylinderNecklacePresentation (underDiagram underCocone)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter

variable {I : Type} [SmallCategory I] {W : Source} {x y : Vertex W}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (L : I ⥤ DecoratedNecklaceHomDiagram.Index W x y)
variable (time : I ⥤ SimplexCategory)
variable (c : codes L ⟶ (Functor.const I).obj Q.code)

private abbrev D := Over.lift (codes L) c
private abbrev T (p : I) := ((D Q L c).obj p).left
private abbrev product :=
  JTJointRelativeParameters.withTime Q.map J time (D Q L c) (whole Q.code)
private abbrev degree :=
  L ⋙ OrderedLabelElements.projection W (boundaryPoint W x y) ⋙
    CategoryTheory.Prod.snd NecklaceCode SimplexCategory

variable {Y : I ⥤ SSet.{0}} (π : Y ⟶ product Q L time c)
variable (θ : Y ⟶ degree (W := W) (x := x) (y := y) L ⋙ J)
variable (hraw : ∀ p, lift (π.app p ≫ fst _ _) (θ.app p) ≫
    JTNecklaceLabelRealization.realizedLabel (T Q L c p).toSSet W
      ((degree (W := W) (x := x) (y := y) L).obj p)
      (JTRealizedLabelEndpoints.orderedLabel W x y (T Q L c p)
        ((degree (W := W) (x := x) (y := y) L).obj p)
        (OrderedLabelElements.label W (boundaryPoint W x y) (L.obj p))) =
    (π.app p ≫ fst _ _) ≫ ((D Q L c).obj p).hom.map ≫ Q.map)

/-- The two literal legs of the full covered evaluation determine its lift
into the original fixed-target pullback diagram. -/
def pullbackLift : JTGraphCoveredLabelEvaluation.reduced Q L time c π ⟶
    L ⋙ JTTargetCommaPullback.diagram W x y Q :=
  JTDecoratedIntervalCylinder.liftFromProjections Q L
    (JTGraphCoveredLabelEvaluation.reduced Q L time c π)
    (JTGraphCoveredLabelEvaluation.decorated Q L time c π θ)
    (JTGraphCoveredLabelEvaluation.nativeLeg Q L time c π)
    (JTGraphCoveredLabelEvaluation.raw_square Q L time c π θ hraw)

/-- Both sides evaluate exactly the same complete internal-necklace
presentation, retaining the original fixed target and the raw proof. -/
theorem evaluation_eq_mapPresentation :
    JTGraphCoveredLabelEvaluation.evaluation Q L time c π θ hraw =
      JTBoundaryNecklacePresentationCone.mapPresentation
        (JTTargetCommaPullback.diagram W x y Q)
        (JTGraphCoveredLabelEvaluation.reduced Q L time c π) L
        (pullbackLift Q L time c π θ hraw) ⋙
          JTTargetCommaExactEvaluation.fromPresentation W x y Q := rfl

end
end DaggerModels.PartII.JTGraphCoveredLiftInterface
