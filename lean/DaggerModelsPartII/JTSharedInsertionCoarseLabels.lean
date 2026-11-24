import DaggerModelsPartII.JTSharedInsertionCoarseChoice
import DaggerModelsPartII.JTVariableMiddleWhiskeredDiagram

/-!
# The actual corrected coarse interval label on the same insertion choices

Reuse the existing paired-gap coefficient and its actual corrected surroundings.
The SAME original all-vertex tuple supplies both outside cuts and all four
correction edges. Reindexing retains the complete common coefficient chain.
This is a decorated-label family only: no raw equation, product parameter,
natural section, point-target evaluation or full insertion comparison is asserted.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTSharedInsertionCoarseLabels

open JTParametrizedTargetFamilies (Family codes)
open JTParametrizedTargetFamilyComparison (degrees)
open JTProjectiveOrderedFiberComparison (row)
open TripleBeadEndpointLabel (labels firstRestriction lastRestriction)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev pre (W : Source) {X Y : SSet.{0}} (f : X ⟶ Y) :=
  diagramMappingPrecomp (ReversalDiscreteFreeColimits.discreteFree.map f) W

private def middleCoefficient {I : Type} [SmallCategory I] {W : Source} (z : Vertex W)
    (M : I ⥤ DecoratedNecklaceHomDiagram.Index W z z) (p : I) :
    std.obj ((degrees M).obj p) ⟶ labels W ((codes M).obj p) :=
  JTOrderedLabelBinaryGlue.coefficient W z z ((codes M).obj p) ((degrees M).obj p)
    (M.obj p).unop.2

private def complete {I : Type} [SmallCategory I] {W : Source} (x z y : Vertex W)
    (M : I ⥤ DecoratedNecklaceHomDiagram.Index W z z) (P R : I ⥤ NecklaceCode)
    (O : JTSupportedPathWhiskeredDiagram.Surroundings W x z y M P R) :
    JTVariableMiddleWhiskeredDiagram.Family
      (W := W) (x := x) (y := y) P (codes M) R (degrees M) where
  data p := {
    left := O.left p
    middle := middleCoefficient z M p
    right := O.right p
    left_join := (O.inner_left p).trans
      (JTOrderedLabelBinaryGlue.coefficient_first W z z ((codes M).obj p)
        ((degrees M).obj p) (M.obj p).unop.2).symm
    right_join := (JTOrderedLabelBinaryGlue.coefficient_last W z z ((codes M).obj p)
      ((degrees M).obj p) (M.obj p).unop.2).trans (O.inner_right p).symm
    first := O.global_first p
    last := O.global_last p }
  left_nat f := O.left_nat f
  middle_nat {p q} f :=
    JTOrderedLabelWedge.coefficient_of_indexHom (W := W) (x := z) (y := z)
      (M.obj p).unop.2 (M.obj q).unop.2 ((codes M).map f) ((degrees M).map f)
      (M.map f) rfl
  right_nat f := O.right_nat f

private def reindexFamily {I B : Type} [SmallCategory I] [SmallCategory B]
    {W : Source} {x y : Vertex W} (G : I ⥤ B)
    {P M R : B ⥤ NecklaceCode} {K : B ⥤ SimplexCategory}
    (C : JTVariableMiddleWhiskeredDiagram.Family
      (W := W) (x := x) (y := y) P M R K) :
    JTVariableMiddleWhiskeredDiagram.Family
      (W := W) (x := x) (y := y) (G ⋙ P) (G ⋙ M) (G ⋙ R) (G ⋙ K) where
  data p := C.data (G.obj p)
  left_nat f := C.left_nat (G.map f)
  middle_nat f := C.middle_nat (G.map f)
  right_nat f := C.right_nat (G.map f)

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

private abbrev z := JTParametrizedBeadGraph.jointCoefficient (Q := Q) j
private abbrev pairFamily := complete x (z j) y
  (JTJointPairWhiskeredSurroundings.middleLabels F j)
  (JTJointPairWhiskeredSurroundings.leftNative F j)
  (JTJointPairWhiskeredSurroundings.rightNative F j)
  (JTJointPairWhiskeredSurroundings.surroundings F j)

/-- The original full common insertion chain, without any new paired choices. -/
abbrev Index := JTSharedInsertionChoices.Index F j

/-- Reuse the two outside choices of the SAME original all-vertex tuple. -/
abbrev base := JTSharedInsertionCoarseChoice.toPairChain F j

/-- The corrected old prefix at a, including its original ending edge. -/
abbrev leftNative := base F j ⋙ JTJointPairWhiskeredSurroundings.leftNative F j

/-- Starting at a, the entire old interval [a,c], and ending at c. -/
abbrev middleNative := base F j ⋙ JTJointPairGapChainLabels.native F j

/-- The corrected old suffix at c, including its original starting edge. -/
abbrev rightNative := base F j ⋙ JTJointPairWhiskeredSurroundings.rightNative F j

/-- The complete common coefficient chain, with every original operator retained. -/
abbrev ordinals := JTSharedInsertionChoices.ordinals F j

/-- Attach both actual corrected surroundings to the complete actual coarse gap label. -/
def family : JTVariableMiddleWhiskeredDiagram.Family
    (W := W) (x := x) (y := y) (leftNative F j) (middleNative F j)
      (rightNative F j) (ordinals F j) :=
  reindexFamily (base F j) (pairFamily F j)

/-- The actual globally pointed coarse decorated-label diagram on shared choices. -/
def labels : Index F j ⥤ DecoratedNecklaceHomDiagram.Index W x y := (family F j).labels

/-- Its native code keeps all three old intervals and all four original correction edges. -/
theorem labels_projection (p : Index F j) :
    (OrderedLabelElements.projection W (OrderedNecklaceVertexPoints.boundaryPoint W x y)).obj
        ((labels F j).obj p) =
      (wedge ((leftNative F j).obj p)
        (wedge ((middleNative F j).obj p) ((rightNative F j).obj p)),
          (ordinals F j).obj p) := rfl

/-- Every original operator acts on all three complete native pieces and the full chain. -/
theorem labels_map_projection {p q : Index F j} (f : p ⟶ q) :
    (OrderedLabelElements.projection W (OrderedNecklaceVertexPoints.boundaryPoint W x y)).map
        ((labels F j).map f) =
      (wedgeMap ((leftNative F j).map f)
        (wedgeMap ((middleNative F j).map f) ((rightNative F j).map f)),
          (ordinals F j).map f) :=
  JTVariableMiddleWhiskeredDiagram.Family.arrow_projection (family F j) f

/-- The coarse label has EXACTLY the given common coefficient degree diagram. -/
theorem labels_degrees : degrees (labels F j) = ordinals F j := rfl

/-- The entire left coefficient comes from the SAME earlier outside pair choice. -/
theorem data_left (p : Index F j) : ((family F j).data p).left =
    (JTJointPairWhiskeredSurroundings.surroundings F j).left ((base F j).obj p) := rfl

/-- The full coarse middle coefficient is the existing paired-gap ordered coefficient. -/
theorem data_middle (p : Index F j) : ((family F j).data p).middle =
    middleCoefficient (z j) (JTJointPairGapChainLabels.labels F j) ((base F j).obj p) := rfl

/-- The entire right coefficient comes from the SAME later outside pair choice. -/
theorem data_right (p : Index F j) : ((family F j).data p).right =
    (JTJointPairWhiskeredSurroundings.surroundings F j).right ((base F j).obj p) := rfl

end
end DaggerModels.PartII.JTSharedInsertionCoarseLabels
