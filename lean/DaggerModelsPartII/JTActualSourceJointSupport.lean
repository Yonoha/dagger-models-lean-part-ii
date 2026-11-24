import DaggerModelsPartII.JTJointTimedEndpointSupport
import DaggerModelsPartII.JTPrismJointOrderedLabel
import DaggerModelsPartII.JTOrderedLabelBinaryGlue

/-!
# Full timed support at an actual source vertex over a target joint
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTActualSourceJointSupport

open JTParametrizedTargetFamilies (Family codes)
open JTTargetJointMarks (Joint)
open JTJointTimedEndpointSupport (vertexBead singleVertex vertexBead_vertex
  sourceVertex_lifts timedParameter timedSupport supportedTimedParameter
  supportedTimedParameter_fac rowCoefficient_at_joint)
open JTParametrizedBeadGraph (fullBeadSupportInclusion jointCoefficient)
open JTProjectiveOrderedFiberComparison (row vertexPoint)
open JTTargetIntervalPullback (sourceInterval)
open JTTargetIntervalGluing (middleInclusion)
open JTPrismJointNormalization (jointRaw)
open ReversalDiscreteFreeColimits OrderedNecklaceVertexPoints

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Input (W : Source) := JTReversalInput.ordinaryInput.obj W
private abbrev Raw (W : Source) := OrdinaryJTRealization.realization.obj (Input W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev std := SSet.stdSimplex.{0}
private abbrev zero := op (⦋0⦌ : SimplexCategory)
private abbrev free := discreteFree.{0}

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (a : A) (j : Joint Q.code)
variable (v : Fin (((codes L).obj a).len + 1))
variable (hv : orderMap (F.collapse.app a).map v = j.val)

private abbrev T := (codes L).obj a
private abbrev k := (JTJointRelativeGraphFamily.coefficient (L := L)).obj a

/-- The original source vertex named by its ordinal coordinate. -/
def sourceVertex : (T (L := L) a).toSSet.obj zero :=
  (T (L := L) a).verticesEquiv.symm (ULift.up v)

include hv in
theorem sourceVertex_target_joint :
    (F.collapse.app a).map.app zero (sourceVertex (L := L) a v) =
      (pointAt Q.code (ULift.up j.val)).app zero
        (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{0}))) := by
  have hpt : pointAt (T (L := L) a) (ULift.up v) ≫ (F.collapse.app a).map =
      pointAt Q.code (ULift.up j.val) := by
    rw [pointAt_comp]
    congr 1
    apply ULift.ext
    exact hv
  have hh := congrFun (NatTrans.congr_app hpt zero)
    (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{0})))
  change (F.collapse.app a).map.app zero
      ((pointAt (T (L := L) a) (ULift.up v)).app zero _) = _ at hh
  have hp : (pointAt (T (L := L) a) (ULift.up v)).app zero
      (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{0}))) = sourceVertex (L := L) a v := by
    change SSet.yonedaEquiv (pointAt (T (L := L) a) (ULift.up v)) = _
    exact pointAt_vertex _ _
  rw [hp] at hh
  exact hh

include hv in
/-- The chosen vertex in the actual full inverse interval. -/
def liftedOverlapVertex :
    (sourceInterval (F.collapse.app a) j j le_rfl).toSSet.obj zero :=
  Classical.choose (sourceVertex_lifts F a j (sourceVertex (L := L) a v)
    (sourceVertex_target_joint F a j v hv))

theorem liftedOverlapVertex_fac :
    (middleInclusion (F.collapse.app a) j).app zero
      (liftedOverlapVertex F a j v hv) = sourceVertex (L := L) a v :=
  Classical.choose_spec (sourceVertex_lifts F a j (sourceVertex (L := L) a v)
    (sourceVertex_target_joint F a j v hv))

include hv in
private abbrev r := vertexBead F a j (liftedOverlapVertex F a j v hv)
include hv in
private abbrev i := r F a j v hv ≫ middleInclusion (F.collapse.app a) j

include hv in
/-- The actual degree-zero bead is the named source point. -/
theorem vertexBead_eq_sourcePoint :
    i F a j v hv = (NecklaceCode.singleIso 0).hom ≫
      pointAt (T (L := L) a) (ULift.up v) := by
  apply (cancel_epi (NecklaceCode.singleIso 0).inv).mp
  have he : (NecklaceCode.singleIso 0).inv ≫
      i F a j v hv = pointAt (T (L := L) a) (ULift.up v) := by
    apply SSet.yonedaEquiv.injective
    change (i F a j v hv).app zero singleVertex =
      (pointAt (T (L := L) a) (ULift.up v)).app zero
        (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{0})))
    have hp : (pointAt (T (L := L) a) (ULift.up v)).app zero
        (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{0}))) = sourceVertex (L := L) a v := by
      change SSet.yonedaEquiv (pointAt (T (L := L) a) (ULift.up v)) = _
      exact pointAt_vertex _ _
    rw [hp]
    change (middleInclusion (F.collapse.app a) j).app zero
      ((r F a j v hv).app zero singleVertex) = _
    rw [vertexBead_vertex, liftedOverlapVertex_fac]
  simpa only [Category.assoc, Iso.inv_hom_id, Category.id_comp] using he

/-- The support degree of the entire independent time prism at this vertex. -/
abbrev usedDegree (hv : orderMap (F.collapse.app a).map v = j.val) : SimplexCategory :=
  timedSupport F a j (liftedOverlapVertex F a j v hv)

/-- Its ordinal inclusion into the original coefficient degree. -/
abbrev usedInclusion (hv : orderMap (F.collapse.app a).map v = j.val) :
    usedDegree F a j v hv ⟶ k (L := L) a :=
  fullBeadSupportInclusion F a 0 (i F a j v hv)

include hv in
theorem usedInclusion_mono : Mono (usedInclusion F a j v hv) :=
  JTRowGraphParameterSupport.inclusion_mono _

/-- The full time-dependent parameter at the named source point. -/
def timeParameter :
    (Δ[0] : SSet.{0}) ⊗ J.obj (time.obj a) ⟶ J.obj (k (L := L) a) :=
  (pointAt (T (L := L) a) (ULift.up v) ⊗ₘ
    𝟙 (J.obj (time.obj a))) ≫ F.parameter a

include hv in
/-- Its exact factor through the used ordinal support. -/
theorem timeParameter_factor :
    supportedTimedParameter F a j (liftedOverlapVertex F a j v hv) ≫
      J.map (usedInclusion F a j v hv) = timeParameter F a v := by
  rw [supportedTimedParameter_fac F a j (liftedOverlapVertex F a j v hv)]
  unfold timeParameter timedParameter JTParametrizedBeadGraph.fullBeadParameter
  change (((NecklaceCode.singleIso 0).inv ≫ i F a j v hv) ⊗ₘ 𝟙 _) ≫ F.parameter a = _
  rw [vertexBead_eq_sourcePoint F a j v hv]
  simp only [Iso.inv_hom_id_assoc]

/-- The full old mapping coefficient of the original ordered label. -/
def oldCoefficient :=
  JTOrderedLabelBinaryGlue.coefficient W x y (T (L := L) a) (k (L := L) a)
    (OrderedLabelElements.label W (OrderedNecklaceVertexPoints.boundaryPoint W x y)
      (L.obj a))

/-- The row-zero map obtained by pulling the old mapping coefficient back to
the actual named source point. -/
def oldVertexRow (v : Fin (((codes L).obj a).len + 1)) :
    std.obj (k (L := L) a) ⟶ row W ⦋0⦌ :=
  oldCoefficient (L := L) a ≫
    diagramMappingPrecomp (free.map (pointAt (T (L := L) a) (ULift.up v))) W ≫
      (OrderedSimplexEndpointFiber.freeSimplexRowIso W 0).hom

include hv in
private theorem oldVertexLabel_eq_bead :
    oldCoefficient (L := L) a ≫
      diagramMappingPrecomp (free.map (pointAt (T (L := L) a) (ULift.up v))) W =
      SSet.yonedaEquiv.symm (JTParametrizedBeadGraph.beadLabel (a := a) 0
        (i F a j v hv)) ≫
        diagramMappingPrecomp (free.map (NecklaceCode.singleIso 0).inv) W := by
  rw [vertexBead_eq_sourcePoint F a j v hv]
  unfold oldCoefficient JTOrderedLabelBinaryGlue.coefficient
  apply SSet.yonedaEquiv.injective
  simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  unfold JTParametrizedBeadGraph.beadLabel
  erw [Equiv.apply_symm_apply]
  change Functor.whiskerRight
      (free.map (pointAt (T (L := L) a) (ULift.up v)))
        (tensorRight (std.obj (k (L := L) a))) ≫
      JTRealizedLabelEndpoints.orderedLabel W x y (T (L := L) a) (k (L := L) a)
        (OrderedLabelElements.label W (boundaryPoint W x y) (L.obj a)) =
    Functor.whiskerRight (free.map (NecklaceCode.singleIso 0).inv)
        (tensorRight (std.obj (k (L := L) a))) ≫
      (Functor.whiskerRight
        (free.map ((NecklaceCode.singleIso 0).hom ≫
          pointAt (T (L := L) a) (ULift.up v)))
          (tensorRight (std.obj (k (L := L) a))) ≫
        JTRealizedLabelEndpoints.orderedLabel W x y (T (L := L) a) (k (L := L) a)
          (OrderedLabelElements.label W (boundaryPoint W x y) (L.obj a)))
  rw [← Category.assoc, ← Functor.whiskerRight_comp, ← free.map_comp,
    Iso.inv_hom_id_assoc]

include hv in
theorem oldVertexRow_eq_bead :
    oldVertexRow (L := L) a v =
      JTParametrizedBeadGraph.coefficient (a := a) 0 (i F a j v hv) := by
  unfold oldVertexRow JTParametrizedBeadGraph.coefficient
  rw [← Category.assoc, oldVertexLabel_eq_bead F a j v hv]
  rfl

include hv in
/-- The old mapping coefficient, restricted along every used time index,
is the constant joint row. -/
theorem oldVertexRow_supported_joint :
    std.map (usedInclusion F a j v hv) ≫ oldVertexRow (L := L) a v =
      SSet.stdSimplex.isTerminalObj₀.from (std.obj (usedDegree F a j v hv)) ≫
        vertexPoint W (jointCoefficient (Q := Q) j) := by
  rw [oldVertexRow_eq_bead F a j v hv]
  let m := usedDegree F a j v hv
  let p := SimplexCategory.isTerminalZero.from m
  let z := jointCoefficient (Q := Q) j
  have hterm : SSet.stdSimplex.isTerminalObj₀.from (std.obj m) = std.map p :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [hterm]
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_map_comp, SSet.yonedaEquiv_map_comp]
  have hz : SSet.yonedaEquiv (vertexPoint W z) = z :=
    Equiv.apply_symm_apply _ _
  rw [hz]
  have h := rowCoefficient_at_joint F a j (liftedOverlapVertex F a j v hv)
  change (Input W).map
      (show (⦋0⦌, m) ⟶ (⦋0⦌, k (L := L) a) from
        (𝟙 ⦋0⦌, usedInclusion F a j v hv)).op
        (SSet.yonedaEquiv (X := row W ⦋0⦌)
          (JTParametrizedBeadGraph.coefficient (a := a) 0 (i F a j v hv))) =
    (Input W).map
      (show (⦋0⦌, m) ⟶ (⦋0⦌, ⦋0⦌) from
        (𝟙 ⦋0⦌, p)).op z
  have ho : SimplexCategory.isTerminalZero.from ⦋0⦌ = 𝟙 ⦋0⦌ :=
    SimplexCategory.isTerminalZero.hom_ext _ _
  simpa only [ho] using h

end

end DaggerModels.PartII.JTActualSourceJointSupport
