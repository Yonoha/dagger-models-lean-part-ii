import DaggerModelsPartII.JTJointPairGapChainLabels
import DaggerModelsPartII.JTSupportedPathWhiskeredDiagram
import DaggerModelsPartII.JTOrderedLabelWedge

/-!
Actual corrected surroundings for the supported path on the common pair-chain
index. Both outer labels already include their ending/starting correction edges,
so their inner endpoints are the literal joint on the WHOLE coefficient simplex.
This derives the existing Surroundings input on the actual exact-pair chain;
no weakness of its projection to the old base or full vertical coherence is claimed.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 150000

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTJointPairWhiskeredSurroundings

open JTProjectiveOrderedFiberComparison (row)
open JTParametrizedTargetFamilies (Family codes)
open JTParametrizedTargetFamilyComparison (degrees)
open JTTargetJointMarks (Joint)
open TripleBeadEndpointLabel (labels)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev pre (W : Source) {X Y : SSet.{0}} (g : X ⟶ Y) :=
  diagramMappingPrecomp (ReversalDiscreteFreeColimits.discreteFree.map g) W

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time) (j : Joint Q.code)

private abbrev I := JTJointPairChainDiagram.Index F j
private abbrev z := JTParametrizedBeadGraph.jointCoefficient (Q := Q) j

/-- The actual padded old gap with both corrected endpoints at the joint. -/
abbrev middleLabels := JTJointPairGapChainLabels.labels F j

/-- The earlier whole left label, including its ending correction edge. -/
abbrev leftSide := JTJointPairChainDiagram.earlier F j ⋙
  JTActualJointChainSideLabels.leftLabels F j

/-- The later whole right label, including its starting correction edge. -/
abbrev rightSide := JTJointPairChainDiagram.later F j ⋙
  JTActualJointChainSideLabels.rightLabels F j

/-- The complete corrected native code of the left surrounding piece. -/
abbrev leftNative := codes (leftSide F j)

/-- The complete corrected native code of the right surrounding piece. -/
abbrev rightNative := codes (rightSide F j)

private abbrev K := degrees (middleLabels F j)

/-- All middle coefficients use the original common full-chain ordinal. -/
theorem middle_degrees : degrees (middleLabels F j) =
    JTJointPairChainDiagram.ordinals F j := rfl

/-- The corrected left piece uses precisely the same full-chain degree. -/
theorem left_degrees : degrees (leftSide F j) =
    JTJointPairChainDiagram.ordinals F j := rfl

/-- The corrected right piece uses precisely the same full-chain degree. -/
theorem right_degrees : degrees (rightSide F j) =
    JTJointPairChainDiagram.ordinals F j := rfl

private def leftCoefficient (p : I F j) :
    std.obj ((K F j).obj p) ⟶ labels W ((leftNative F j).obj p) :=
  JTOrderedLabelBinaryGlue.coefficient W x (z j) ((leftNative F j).obj p)
    ((K F j).obj p) ((leftSide F j).obj p).unop.2

private def rightCoefficient (p : I F j) :
    std.obj ((K F j).obj p) ⟶ labels W ((rightNative F j).obj p) :=
  JTOrderedLabelBinaryGlue.coefficient W (z j) y ((rightNative F j).obj p)
    ((K F j).obj p) ((rightSide F j).obj p).unop.2

private theorem left_natural {p q : I F j} (f : p ⟶ q) :
    leftCoefficient F j p = std.map ((K F j).map f) ≫
      leftCoefficient F j q ≫ pre W ((leftNative F j).map f).map := by
  exact JTOrderedLabelWedge.coefficient_of_indexHom (W := W) (x := x) (y := z j)
    ((leftSide F j).obj p).unop.2 ((leftSide F j).obj q).unop.2
    ((leftNative F j).map f) ((K F j).map f) ((leftSide F j).map f) (by rfl)

private theorem right_natural {p q : I F j} (f : p ⟶ q) :
    rightCoefficient F j p = std.map ((K F j).map f) ≫
      rightCoefficient F j q ≫ pre W ((rightNative F j).map f).map := by
  exact JTOrderedLabelWedge.coefficient_of_indexHom (W := W) (x := z j) (y := y)
    ((rightSide F j).obj p).unop.2 ((rightSide F j).obj q).unop.2
    ((rightNative F j).map f) ((K F j).map f) ((rightSide F j).map f) (by rfl)

/-- The actual corrected pair-chain supplies all outer coefficients, their
naturality and four WHOLE-coefficient endpoint laws without a new surroundings premise. -/
def surroundings : JTSupportedPathWhiskeredDiagram.Surroundings W x (z j) y
    (middleLabels F j) (leftNative F j) (rightNative F j) where
  left := leftCoefficient F j
  right := rightCoefficient F j
  left_nat f := left_natural F j f
  right_nat f := right_natural F j f
  global_first p := JTOrderedLabelBinaryGlue.coefficient_first W x (z j)
    ((leftNative F j).obj p) ((K F j).obj p) ((leftSide F j).obj p).unop.2
  inner_left p := JTOrderedLabelBinaryGlue.coefficient_last W x (z j)
    ((leftNative F j).obj p) ((K F j).obj p) ((leftSide F j).obj p).unop.2
  inner_right p := JTOrderedLabelBinaryGlue.coefficient_first W (z j) y
    ((rightNative F j).obj p) ((K F j).obj p) ((rightSide F j).obj p).unop.2
  global_last p := JTOrderedLabelBinaryGlue.coefficient_last W (z j) y
    ((rightNative F j).obj p) ((K F j).obj p) ((rightSide F j).obj p).unop.2

end
end DaggerModels.PartII.JTJointPairWhiskeredSurroundings
