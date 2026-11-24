import DaggerModelsPartII.JTChosenSeamOldComparison
import DaggerModelsPartII.JTActualSourceJointSupport
import DaggerModelsPartII.JTWhiskeredGraphRaw

/-!
The original three-piece label has middle code `single 0`. We identify its
actual middle vertex row with the supplied row `f`, using the three-piece
coefficient restriction and the native point of `single 0`. The existing
actual-source joint support theorem then gives stationarity on the full used
time face. This assumes a natural supplied surroundings family `O`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTThreePieceMiddleSupport

open JTProjectiveOrderedFiberComparison (row vertexPoint)
open JTParametrizedTargetFamilies (codes Family)
open JTTargetJointMarks (Joint)
open ReversalDiscreteFreeColimits (discreteFree)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev J := GroupoidSimplex.parameter
private abbrev pre (W : Source) {X Y : SSet.{0}} (u : X ⟶ Y) :=
  diagramMappingPrecomp (discreteFree.map u) W

variable {I : Type} [SmallCategory I] (W : Source)
variable {x y : Vertex W} (P R : I ⥤ NecklaceCode)

/-- The unique native vertex of the middle `single 0` inside the right-associated triple. -/
def middleVertex (a : I) :
    Fin ((wedge (P.obj a) (wedge (single 0) (R.obj a))).len + 1) :=
  wedgeRight (P.obj a) (wedge (single 0) (R.obj a))
    (wedgeLeft (single 0) (R.obj a) 0)

/-- The canonical middle vertex is the image of the sole native middle point. -/
theorem middlePoint (a : I) :
    pointAt (wedge (P.obj a) (wedge (single 0) (R.obj a)))
        (ULift.up (middleVertex P R a)) =
      pointAt (single 0) (ULift.up 0) ≫
        tripleRightU (P.obj a) (single 0) (R.obj a) := by
  unfold tripleRightU
  rw [← Category.assoc, pointAt_comp, wedgeιLeft_vertices,
    pointAt_comp, wedgeιRight_vertices]
  rfl

variable (K : I ⥤ SimplexCategory)
variable (f : K ⋙ std ⟶ (Functor.const I).obj (row W ⦋0⦌))
variable (O : JTChosenSeamChainDiagram.Surroundings W K f P R x y)

private theorem old_coefficient (a : I) :
    JTActualSourceJointSupport.oldCoefficient
      (L := (JTChosenSeamOldComparison.oldFamily W K f O).labels) a =
        JTComposedPrismLabels.coefficient
          (JTThreePieceLabelOperators.coefficients
            (JTChosenSeamOldComparison.oldData W K f O a)) := by
  unfold JTActualSourceJointSupport.oldCoefficient
  change JTOrderedLabelBinaryGlue.coefficient W x y _ _
      (JTComposedPrismLabels.orderedPoint
        (JTThreePieceLabelOperators.coefficients
          (JTChosenSeamOldComparison.oldData W K f O a))) = _
  unfold JTOrderedLabelBinaryGlue.coefficient
  rw [JTComposedPrismLabels.orderedPoint_coefficient]
  simp only [Equiv.symm_apply_apply]

omit [SmallCategory I] in
private theorem middlePoint_row :
    JTNativeRowLabel.labelFromRow W 0 ≫
      pre W (pointAt (single 0) (ULift.up 0)) ≫
        (OrderedSimplexEndpointFiber.freeSimplexRowIso W 0).hom =
      𝟙 (row W ⦋0⦌) := by
  unfold JTNativeRowLabel.labelFromRow pre
  have hp : pointAt (single 0) (ULift.up 0) ≫ (singleIso 0).hom =
      𝟙 (std.obj ⦋0⦌) := by
    rw [JTNativeRowLabel.nativeVertex]
    exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  calc
    _ = (OrderedSimplexEndpointFiber.freeSimplexRowIso W 0).inv ≫
        (diagramMappingPrecomp (discreteFree.map (singleIso 0).hom) W ≫
          diagramMappingPrecomp (discreteFree.map
            (pointAt (single 0) (ULift.up 0))) W) ≫
          (OrderedSimplexEndpointFiber.freeSimplexRowIso W 0).hom := by
            simp only [Category.assoc]
    _ = (OrderedSimplexEndpointFiber.freeSimplexRowIso W 0).inv ≫
        diagramMappingPrecomp (discreteFree.map
          (pointAt (single 0) (ULift.up 0) ≫ (singleIso 0).hom)) W ≫
          (OrderedSimplexEndpointFiber.freeSimplexRowIso W 0).hom := by
            rw [← diagramMappingPrecomp_comp, ← discreteFree.map_comp]
    _ = _ := by
      rw [hp, discreteFree.map_id, diagramMappingPrecomp_id]
      exact Iso.inv_hom_id _

private theorem generic_middle_row (a : I)
    (D : JTThreePieceLabelOperators.Data W (P.obj a) (single 0)
      (R.obj a) (K.obj a) x y)
    (r : std.obj (K.obj a) ⟶ row W ⦋0⦌)
    (hr : D.middle = r ≫ JTNativeRowLabel.labelFromRow W 0) :
    JTComposedPrismLabels.coefficient (JTThreePieceLabelOperators.coefficients D) ≫
      pre W (pointAt (wedge (P.obj a) (wedge (single 0) (R.obj a)))
        (ULift.up (middleVertex P R a))) ≫
      (OrderedSimplexEndpointFiber.freeSimplexRowIso W 0).hom = r := by
  rw [middlePoint P R a]
  have hpre : pre W (pointAt (single 0) (ULift.up 0) ≫
      tripleRightU (P.obj a) (single 0) (R.obj a)) =
        pre W (tripleRightU (P.obj a) (single 0) (R.obj a)) ≫
          pre W (pointAt (single 0) (ULift.up 0)) := by
    unfold pre
    rw [discreteFree.map_comp, diagramMappingPrecomp_comp]
  rw [hpre]
  simp only [← Category.assoc]
  rw [JTWhiskeredGraphRaw.coefficient_middle W D, hr]
  calc
    _ = r ≫ (JTNativeRowLabel.labelFromRow W 0 ≫
        pre W (pointAt (single 0) (ULift.up 0)) ≫
          (OrderedSimplexEndpointFiber.freeSimplexRowIso W 0).hom) := by
            simp only [Category.assoc]
    _ = r := by rw [middlePoint_row W, Category.comp_id]

/-- The actual old ordered coefficient at the canonical middle vertex is `f`. -/
theorem middleVertex_row (a : I) :
    JTActualSourceJointSupport.oldVertexRow
      (L := (JTChosenSeamOldComparison.oldFamily W K f O).labels)
        a (middleVertex P R a) = f.app a := by
  unfold JTActualSourceJointSupport.oldVertexRow
  rw [old_coefficient W P R K f O a]
  exact generic_middle_row W P R K a
    (JTChosenSeamOldComparison.oldData W K f O a) (f.app a) rfl

variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (time : I ⥤ SimplexCategory)
variable (oldTimed : Family Q (JTChosenSeamOldComparison.oldFamily W K f O).labels time)
variable (a : I) (j : Joint Q.code)
variable (hv : orderMap (oldTimed.collapse.app a).map (middleVertex P R a) = j.val)

/-- On the actual full used time face, the supplied middle row is the joint row. -/
theorem middleVertex_supported_joint :
    std.map (JTActualSourceJointSupport.usedInclusion oldTimed a j
      (middleVertex P R a) hv) ≫ f.app a =
      SSet.stdSimplex.isTerminalObj₀.from
          (std.obj (JTActualSourceJointSupport.usedDegree oldTimed a j
            (middleVertex P R a) hv)) ≫
        vertexPoint W (JTParametrizedBeadGraph.jointCoefficient j) := by
  rw [← middleVertex_row W P R K f O a]
  exact JTActualSourceJointSupport.oldVertexRow_supported_joint oldTimed a j
    (middleVertex P R a) hv

/-- The original full timed parameter at the middle point factors through
the same actual used face on which its row is stationary. -/
theorem middleVertex_timeParameter_factor :
    JTJointTimedEndpointSupport.supportedTimedParameter oldTimed a j
        (JTActualSourceJointSupport.liftedOverlapVertex oldTimed a j
          (middleVertex P R a) hv) ≫
      J.map (JTActualSourceJointSupport.usedInclusion oldTimed a j
        (middleVertex P R a) hv) =
    JTActualSourceJointSupport.timeParameter oldTimed a (middleVertex P R a) :=
  JTActualSourceJointSupport.timeParameter_factor oldTimed a j
    (middleVertex P R a) hv

end
end DaggerModels.PartII.JTThreePieceMiddleSupport
