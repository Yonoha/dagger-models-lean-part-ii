import DaggerModelsPartII.JTSharedInsertionCoarseMiddleSupport
import DaggerModelsPartII.JTSupportedPathWhiskeredGraph

/-!
# The actual coarse label as the old endpoint of the supported whiskered path

Reindex the existing corrected pair surroundings along the SAME outside pair
of the actual insertion choices. The resulting old three-piece family is the
already checked coarse family, including its complete coefficients and every
original operator. No new surroundings, coefficient compatibility, support or
parameter section is assumed. This supplies data, not a full contraction.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTSharedInsertionCoarseWhiskeredData

open JTParametrizedTargetFamilies (Family codes)
open JTParametrizedTargetFamilyComparison (degrees)
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

private def reindexSurroundings {I B : Type} [SmallCategory I] [SmallCategory B]
    {W : Source} {x z y : Vertex W} (G : I ⥤ B)
    {M : B ⥤ DecoratedNecklaceHomDiagram.Index W z z} {P R : B ⥤ NecklaceCode}
    (O : JTSupportedPathWhiskeredDiagram.Surroundings W x z y M P R) :
    JTSupportedPathWhiskeredDiagram.Surroundings W x z y (G ⋙ M) (G ⋙ P) (G ⋙ R) where
  left p := O.left (G.obj p)
  right p := O.right (G.obj p)
  left_nat f := O.left_nat (G.map f)
  right_nat f := O.right_nat (G.map f)
  global_first p := O.global_first (G.obj p)
  inner_left p := O.inner_left (G.obj p)
  inner_right p := O.inner_right (G.obj p)
  global_last p := O.global_last (G.obj p)

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

private abbrev z := JTParametrizedBeadGraph.jointCoefficient (Q := Q) j

/-- The unchanged original insertion-choice category. -/
abbrev Index := JTSharedInsertionChoices.Index F j

/-- The actual middle, with both correction edges and the whole old chart. -/
abbrev middleLabels := JTSharedInsertionCoarseMiddleSupport.middleLabels F j

/-- The entire corrected left surrounding necklace. -/
abbrev leftNative := JTSharedInsertionCoarseLabels.leftNative F j

/-- The entire corrected right surrounding necklace. -/
abbrev rightNative := JTSharedInsertionCoarseLabels.rightNative F j

/-- All left and right coefficients and four endpoint equations, on every
original insertion-choice operator, without an extra surroundings premise. -/
def surroundings : JTSupportedPathWhiskeredDiagram.Surroundings W x (z j) y
    (middleLabels F j) (leftNative F j) (rightNative F j) :=
  reindexSurroundings (JTSharedInsertionCoarseChoice.toPairChain F j)
    (JTJointPairWhiskeredSurroundings.surroundings F j)

/-- The middle uses precisely the complete shared coefficient degree. -/
theorem middle_degrees : degrees (middleLabels F j) =
    JTSharedInsertionChoices.ordinals F j := rfl

/-- The existing supported-path old family, instantiated with actual data. -/
abbrev oldFamily := JTSupportedPathWhiskeredGraph.oldFamily W x (z j) y
  (middleLabels F j) (leftNative F j) (rightNative F j) (surroundings F j)

/-- Its full coefficients agree with the actual coarse family. -/
theorem oldFamily_eq : oldFamily F j = JTSharedInsertionCoarseLabels.family F j := rfl

/-- Equality includes the complete decorated functor and every original operator. -/
theorem oldLabels_eq : (oldFamily F j).labels =
    JTSharedInsertionCoarseLabels.labels F j :=
  congrArg (fun C ↦ C.labels) (oldFamily_eq F j)

/-- The entire left coefficient is the original coarse left coefficient. -/
theorem surroundings_left (p : Index F j) :
    (surroundings F j).left p = ((JTSharedInsertionCoarseLabels.family F j).data p).left :=
  rfl

/-- The entire right coefficient is the original coarse right coefficient. -/
theorem surroundings_right (p : Index F j) :
    (surroundings F j).right p =
      ((JTSharedInsertionCoarseLabels.family F j).data p).right := rfl

end
end DaggerModels.PartII.JTSharedInsertionCoarseWhiskeredData
