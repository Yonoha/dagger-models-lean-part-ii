import DaggerModelsPartII.JTEndpointGraphOverlapSquares
import DaggerModelsPartII.JTBoundaryNecklacePresentationTimeChange

/-! Compare all internal necklaces of each original chart to the joined evaluation. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTEndpointGraphOverlapComparison

open OrdinaryJTRealization (realization)
open JTReversalInput (ordinaryInput)
open JTProjectiveOrderedFiberComparison (row)
open JTMixedGraphEndpointLifts (vertex)
open JTEndpointGraphCoefficientSlice (MixedGraphs)
open JTEndpointGraphCoefficientOverlap
open JTEndpointGraphOverlapChoices
open JTEndpointGraphOverlapFamilies (dim toFixedBead)
open JTEndpointGraphOverlapRestriction
open JTEndpointGraphOverlapLabels
open JTEndpointGraphOverlapEvaluation (sourceCylinders labelIndex lifts evaluation)
open BoundaryNecklaceComma (fiberDiagram)

noncomputable section

private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : SegalLocalizers.ReverseDaggerSpace.{0}} {d m : ℕ}
variable {q : (Δ[d] : SSet.{0}) ⟶ realization.obj (ordinaryInput.obj W)}
variable (P : MixedGraphs q) (parents : Fin (m + 1) → MixedGraphs q)
variable (refineTo : ∀ e, parents e ⟶ P)
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (hx : SSet.yonedaEquiv (vertex ⦋d⦌ 0 ≫ q) = rawVertex W x)
variable (hy : SSet.yonedaEquiv (vertex ⦋d⦌ (Fin.last d) ≫ q) = rawVertex W y)

private abbrev Q := JTNormalizedGraphTargetArrow.target hx hy
private abbrev I := Index P parents refineTo hx hy

variable (e : Fin (m + 1))

private abbrev R := toSide P parents refineTo hx hy e
private abbrev C := JTEndpointGraphCoefficientEvaluation.cylinders (parents e) hx hy

private abbrev JoinedCylinders := sourceCylinders P parents refineTo hx hy
private abbrev OldLabels :=
  JTEndpointGraphCoefficientLabels.labelIndex (parents e) hx hy
private abbrev JoinedLabels := labelIndex P parents refineTo hx hy
private abbrev D := JTTargetCommaPullback.diagram W x y (Q hx hy)
private abbrev J := JTTargetCommaExactEvaluation.fromPresentation W x y (Q hx hy)

set_option maxHeartbeats 800000 in
private def presentationComparison :=
  JTBoundaryNecklacePresentationTransport.comparisonReindexedWithSourceChange
    (E := D hx hy)
    (F := C parents hx hy e)
    (F₀ := JoinedCylinders P parents refineTo hx hy)
    (L := OldLabels parents hx hy e)
    (L₀ := JoinedLabels P parents refineTo hx hy)
    (R P parents refineTo hx hy e)
    (JTEndpointGraphCoefficientEvaluation.lifts (parents e) hx hy)
    (lifts P parents refineTo hx hy)
    (timeInclusion P parents refineTo hx hy e)
    (toBridgeLabel P parents refineTo hx hy e)
    (comparisonSquare P parents refineTo hx hy e)

private def comparisonCore :=
  (Functor.associator
    (Grothendieck.pre (fiberDiagram (C parents hx hy e)) (R P parents refineTo hx hy e))
    (JTBoundaryNecklacePresentationCone.mapPresentation (D hx hy)
      (C parents hx hy e) (OldLabels parents hx hy e)
      (JTEndpointGraphCoefficientEvaluation.lifts (parents e) hx hy))
    (J hx hy)).inv ≫
  Functor.whiskerRight (presentationComparison P parents refineTo hx hy e) (J hx hy) ≫
  (Functor.associator
    (toJoined P parents refineTo hx hy e)
    (JTBoundaryNecklacePresentationCone.mapPresentation (D hx hy)
      (JoinedCylinders P parents refineTo hx hy)
      (JoinedLabels P parents refineTo hx hy)
      (lifts P parents refineTo hx hy))
    (J hx hy)).hom

set_option maxHeartbeats 1500000 in
/-- The comparison between the reindexed old and joined fixed-target evaluations. -/
def comparison :
    Grothendieck.pre (fiberDiagram (C parents hx hy e)) (R P parents refineTo hx hy e) ⋙
      JTEndpointGraphCoefficientEvaluation.evaluation (parents e) hx hy ⟶
    toJoined P parents refineTo hx hy e ⋙ evaluation P parents refineTo hx hy :=
  comparisonCore P parents refineTo hx hy e

end
end DaggerModels.PartII.JTEndpointGraphOverlapComparison
