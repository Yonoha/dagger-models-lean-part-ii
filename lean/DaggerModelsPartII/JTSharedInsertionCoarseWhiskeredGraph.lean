import DaggerModelsPartII.JTSharedInsertionCoarseWhiskeredData
import DaggerModelsPartII.JTSharedInsertionCoarseRaw

/-!
# The actual coarse whole graph and raw equation for the whiskered path

The existing coarse graph already contains all original-time coefficient lifts.
Read that SAME graph in the old-product interface of the supported whiskered
path. The complete original raw equation gives its old three-piece raw input;
no new Family, product parameter, raw compatibility or section is assumed.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSharedInsertionCoarseWhiskeredGraph

open JTParametrizedTargetFamilies (Family codes)
open JTParametrizedTargetFamilyComparison (degrees)
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev J := GroupoidSimplex.parameter

private theorem composed_coefficient {W : Source} {x y : Vertex W}
    {P M R : NecklaceCode} {k : SimplexCategory}
    (D : JTThreePieceLabelOperators.Data W P M R k x y) :
    JTOrderedLabelBinaryGlue.coefficient W x y (wedge P (wedge M R)) k
        (JTThreePieceLabelOperators.index D).unop.2 =
      JTComposedPrismLabels.coefficient (JTThreePieceLabelOperators.coefficients D) := by
  change SSet.yonedaEquiv.symm (JTRealizedLabelEndpoints.orderedLabel W x y _ _
    (JTComposedPrismLabels.orderedPoint (JTThreePieceLabelOperators.coefficients D))) = _
  rw [JTComposedPrismLabels.orderedPoint_coefficient]
  exact Equiv.symm_apply_apply _ _

private theorem raw_of_ordered {W : Source} {x y : Vertex W}
    {P M R : NecklaceCode} {k : SimplexCategory} {X : SSet.{0}}
    (D : JTThreePieceLabelOperators.Data W P M R k x y)
    (h : X ⟶ (wedge P (wedge M R)).toSSet) (theta : X ⟶ J.obj k)
    (g : (wedge P (wedge M R)).toSSet ⟶ Raw W)
    (H : lift h theta ≫ JTNecklaceLabelRealization.realizedLabel
      (wedge P (wedge M R)).toSSet W k
      (SSet.yonedaEquiv (JTOrderedLabelBinaryGlue.coefficient W x y
        (wedge P (wedge M R)) k (JTThreePieceLabelOperators.index D).unop.2)) = h ≫ g) :
    lift h theta ≫ JTNecklaceLabelRealization.realizedLabel
        (wedge P (wedge M R)).toSSet W k
        (SSet.yonedaEquiv (JTComposedPrismLabels.coefficient
          (JTThreePieceLabelOperators.coefficients D))) = h ≫ g := by
  rw [composed_coefficient D] at H
  exact H

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

private abbrev z := JTParametrizedBeadGraph.jointCoefficient (Q := Q) j
private abbrev M := JTSharedInsertionCoarseWhiskeredData.middleLabels F j
private abbrev P := JTSharedInsertionCoarseWhiskeredData.leftNative F j
private abbrev R := JTSharedInsertionCoarseWhiskeredData.rightNative F j
private abbrev O := JTSharedInsertionCoarseWhiskeredData.surroundings F j

/-- The SAME shared insertion choices and full coefficient chain. -/
abbrev Index := JTSharedInsertionCoarseWhiskeredData.Index F j

/-- The already derived old three-piece family, with all original operators. -/
abbrev oldFamily := JTSharedInsertionCoarseWhiskeredData.oldFamily F j

/-- Its complete decorated label diagram in the original global endpoints. -/
abbrev oldLabels := (oldFamily F j).labels

/-- The entire original time, distinct from the shared choice clock. -/
abbrev oldTime := JTSharedInsertionCoarseGraph.oldTime F j

/-- Every original-time coefficient lift of the actual coarse label is retained. -/
abbrev graph := JTSharedInsertionCoarseGraph.graph F j

/-- The literal old native/time product required by the supported whiskered path. -/
abbrev oldProduct := JTSupportedPathWhiskeredGraph.oldProduct W x (z j) y
  (M F j) (P F j) (R F j) (O F j) (oldTime F j)

/-- The original complete coarse native/time coordinate, without a new parameter choice. -/
def projection : graph F j ⟶ oldProduct F j :=
  JTSharedInsertionCoarseGraph.projection F j

/-- The exact GIVEN shared coefficient parameter in the actual middle degree. -/
def parameter : graph F j ⟶ degrees (M F j) ⋙ J :=
  JTSharedInsertionCoarseGraph.parameter F j

/-- Keep the SAME complete native map into original Q. -/
def target : codes (oldLabels F j) ⟶ (Functor.const (Index F j)).obj Q.code :=
  JTSharedInsertionCoarseNative.target F j

/-- Both product representations use literally the same complete graph component. -/
theorem projection_app (p : Index F j) :
    ((projection F j).app p : (graph F j).obj p ⟶
      (JTSharedInsertionCoarseGraph.X F j).obj p) =
    (JTSharedInsertionCoarseGraph.projection F j).app p := rfl

/-- The coefficient parameter is the original graph parameter, not a chosen lift. -/
theorem parameter_app (p : Index F j) :
    ((parameter F j).app p : (graph F j).obj p ⟶
      J.obj ((JTSharedInsertionChoices.ordinals F j).obj p)) =
    (JTSharedInsertionCoarseGraph.parameter F j).app p := rfl

/-- The old fixed-target map is the entire actual coarse native target. -/
theorem target_app (p : Index F j) : (target F j).app p =
    (JTSharedInsertionCoarseNative.target F j).app p := rfl

/-- Read the full native coordinate of every given graph point. -/
abbrev nativeCoordinate (p : Index F j) : (graph F j).obj p ⟶
    (wedge ((P F j).obj p) (wedge ((codes (M F j)).obj p) ((R F j).obj p))).toSSet :=
  (projection F j).app p ≫ fst _ (J.obj ((oldTime F j).obj p))

/-- The exact original whole graph still weakly covers every whole native/time product. -/
theorem projection_trivialFibration (p : Index F j) :
    trivialFibrations SSet.{0} ((projection F j).app p) :=
  JTSharedInsertionCoarseGraph.projection_trivialFibration F j p

set_option maxHeartbeats 400000 in
private def actualRaw (p : Index F j) :=
  raw_of_ordered ((oldFamily F j).data p) (nativeCoordinate F j p)
    ((parameter F j).app p) (((target F j).app p).map ≫ Q.map)
    (JTSharedInsertionCoarseRaw.ordered_raw F j p)

/-- The complete raw input of WhiskeredRaw/Zero/One, derived from original F,j only. -/
theorem oldRaw (p : Index F j) :
    lift (nativeCoordinate F j p) ((parameter F j).app p) ≫
        JTNecklaceLabelRealization.realizedLabel
          (wedge ((P F j).obj p)
            (wedge ((codes (M F j)).obj p) ((R F j).obj p))).toSSet W
          ((degrees (M F j)).obj p)
          (SSet.yonedaEquiv (JTComposedPrismLabels.coefficient
            (JTThreePieceLabelOperators.coefficients ((oldFamily F j).data p)))) =
      nativeCoordinate F j p ≫ ((target F j).app p).map ≫ Q.map :=
  actualRaw F j p

end

end DaggerModels.PartII.JTSharedInsertionCoarseWhiskeredGraph
