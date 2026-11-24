import DaggerModelsPartII.JTWhiskeredGraphRawTransport
import DaggerModelsPartII.JTOrderedLabelWedge

/-!
# Raw transport along one actual decorated-label arrow

The ordered-label arrow supplies its coefficient equation. A compatible map
between arbitrary graph domains then pulls the target raw equation back to the
source. No coefficient section or whole-product Family is required.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphCoveredRawTransport

open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTNecklaceLabelRealization (realizedLabel)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev J := GroupoidSimplex.parameter
private abbrev std := SSet.stdSimplex.{0}
private abbrev pre (W : Source) {S T : SSet.{0}} (n : S ⟶ T) :=
  diagramMappingPrecomp (ReversalDiscreteFreeColimits.discreteFree.map n) W

variable {W : Source} {x y : Vertex W}

private abbrev Index := DecoratedNecklaceHomDiagram.Index W x y
private abbrev pr := OrderedLabelElements.projection W (boundaryPoint W x y)
private abbrev code (i : Index (W := W) (x := x) (y := y)) := (pr.obj i).1
private abbrev degree (i : Index (W := W) (x := x) (y := y)) := (pr.obj i).2
private abbrev label (i : Index (W := W) (x := x) (y := y)) :=
  OrderedLabelElements.label W (boundaryPoint W x y) i
private abbrev coefficient (i : Index (W := W) (x := x) (y := y)) :=
  JTOrderedLabelBinaryGlue.coefficient W x y (code i) (degree i) (label i)
private abbrev ordered (i : Index (W := W) (x := x) (y := y)) :=
  JTRealizedLabelEndpoints.orderedLabel W x y (code i) (degree i) (label i)

private theorem coefficient_ordered (i : Index (W := W) (x := x) (y := y)) :
    SSet.yonedaEquiv (coefficient i) = ordered i :=
  SSet.yonedaEquiv.apply_symm_apply _

variable {i j : Index (W := W) (x := x) (y := y)}

/-- Both projected operators of a decorated arrow give its exact coefficient equation. -/
theorem coefficient_eq (f : i ⟶ j) :
    coefficient i = std.map (pr.map f).2 ≫ coefficient j ≫ pre W (pr.map f).1.map :=
  JTOrderedLabelWedge.coefficient_of_indexHom (label i) (label j)
    (pr.map f).1 (pr.map f).2 f rfl

/-- An exact target ordered raw equation pulls back along a graph map preserving
the native and coefficient coordinates of the actual decorated arrow. -/
theorem ordered_raw (f : i ⟶ j) {X Y : SSet.{0}}
    (h : X ⟶ (code i).toSSet) (q : X ⟶ J.obj (degree i))
    (h' : Y ⟶ (code j).toSSet) (q' : Y ⟶ J.obj (degree j))
    (η : X ⟶ Y) (g : (code j).toSSet ⟶ Raw W)
    (hn : h ≫ (pr.map f).1.map = η ≫ h')
    (hq : q ≫ J.map (pr.map f).2 = η ≫ q')
    (target_raw : lift h' q' ≫
      realizedLabel (code j).toSSet W (degree j) (ordered j) = h' ≫ g) :
    lift h q ≫ realizedLabel (code i).toSSet W (degree i) (ordered i) =
      h ≫ (pr.map f).1.map ≫ g := by
  have hr : lift h' q' ≫ realizedLabel (code j).toSSet W (degree j)
      (SSet.yonedaEquiv (coefficient j)) = h' ≫ g := by
    exact (congrArg (fun a ↦ lift h' q' ≫
      realizedLabel (code j).toSSet W (degree j) a) (coefficient_ordered j)).trans target_raw
  have hs := JTWhiskeredGraphRawTransport.raw W h' q' (coefficient j) g hr h q η
    (pr.map f).1.map (pr.map f).2 (coefficient i) (coefficient_eq f) hn.symm hq
  exact (congrArg (fun a ↦ lift h q ≫
    realizedLabel (code i).toSSet W (degree i) a) (coefficient_ordered i)).symm.trans hs

end
end DaggerModels.PartII.JTGraphCoveredRawTransport
