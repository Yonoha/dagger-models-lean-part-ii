import DaggerModelsPartII.JTActualSourceJointSupport
import DaggerModelsPartII.JTParametrizedBeadGraphOperators

/-!
# Transport of timed joint support under exact source operators
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTActualSourceJointSupportTransport

open JTParametrizedTargetFamilies (Family codes)
open JTTargetJointMarks (Joint)
open JTActualSourceJointSupport (liftedOverlapVertex usedDegree usedInclusion
  timeParameter timeParameter_factor oldVertexRow oldVertexRow_eq_bead)
open JTJointTimedEndpointSupport (vertexBead supportedTimedParameter supportedTimedParameter_fac)
open JTTargetIntervalGluing (middleInclusion)
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev std := SSet.stdSimplex.{0}

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code)
variable {a b : A} (f : a ⟶ b)
variable (v : Fin (((codes L).obj a).len + 1))
variable (v' : Fin (((codes L).obj b).len + 1))
variable (hv : orderMap (F.collapse.app a).map v = j.val)
variable (hv' : orderMap (F.collapse.app b).map v' = j.val)
variable (hvertex : orderMap (((codes L).map f).map) v = v')

private abbrev kf := (JTJointRelativeGraphFamily.coefficient (L := L)).map f
private abbrev sourceBead (c : A) (w : Fin (((codes L).obj c).len + 1))
    (hw : orderMap (F.collapse.app c).map w = j.val) :=
  vertexBead F c j (liftedOverlapVertex F c j w hw) ≫
    middleInclusion (F.collapse.app c) j

include hvertex in
/-- A source operator carrying the selected vertex carries its actual point
map to the selected point map. -/
theorem pointAt_map :
    pointAt ((codes L).obj a) (ULift.up v) ≫ ((codes L).map f).map =
      pointAt ((codes L).obj b) (ULift.up v') := by
  rw [pointAt_comp]
  congr 1
  apply ULift.ext
  exact hvertex

include hvertex in
/-- The full independent time prism parameter commutes with the source and
coefficient operators. -/
theorem timeParameter_map :
    (𝟙 (Δ[0] : SSet.{0}) ⊗ₘ J.map (time.map f)) ≫ timeParameter F b v' =
      timeParameter F a v ≫ J.map (kf (L := L) f) := by
  let c := ((codes L).map f).map
  let t := J.map (time.map f)
  let p := pointAt ((codes L).obj a) (ULift.up v)
  have hp : p ≫ c = pointAt ((codes L).obj b) (ULift.up v') :=
    pointAt_map f v v' hvertex
  have hF : (c ⊗ₘ t) ≫ F.parameter b =
      F.parameter a ≫ J.map (kf (L := L) f) := F.parameter_map f
  change (𝟙 (Δ[0] : SSet.{0}) ⊗ₘ t) ≫
      ((pointAt ((codes L).obj b) (ULift.up v') ⊗ₘ 𝟙 _) ≫ F.parameter b) =
    (p ⊗ₘ 𝟙 _) ≫ F.parameter a ≫ J.map (kf (L := L) f)
  calc
    _ = ((p ≫ c) ⊗ₘ t) ≫ F.parameter b := by
      rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, hp,
        Category.comp_id]
    _ = ((p ⊗ₘ 𝟙 _) ≫ (c ⊗ₘ t)) ≫ F.parameter b := by
      simp only [tensorHom_comp_tensorHom, Category.id_comp]
    _ = (p ⊗ₘ 𝟙 _) ≫ ((c ⊗ₘ t) ≫ F.parameter b) := Category.assoc _ _ _
    _ = (p ⊗ₘ 𝟙 _) ≫ (F.parameter a ≫ J.map (kf (L := L) f)) := by rw [hF]
    _ = (p ⊗ₘ 𝟙 _) ≫ F.parameter a ≫ J.map (kf (L := L) f) :=
      (Category.assoc _ _ _).symm

private theorem timedParameter_eq (c : A) (w : Fin (((codes L).obj c).len + 1))
    (hw : orderMap (F.collapse.app c).map w = j.val) :
    JTJointTimedEndpointSupport.timedParameter F c j (liftedOverlapVertex F c j w hw) =
      timeParameter F c w := by
  exact (supportedTimedParameter_fac F c j (liftedOverlapVertex F c j w hw)).symm.trans
    (timeParameter_factor F c j w hw)

include hvertex in
private theorem timedParameter_map :
    (𝟙 (Δ[0] : SSet.{0}) ⊗ₘ J.map (time.map f)) ≫
      JTJointTimedEndpointSupport.timedParameter F b j
      (liftedOverlapVertex F b j v' hv') =
      JTJointTimedEndpointSupport.timedParameter F a j
        (liftedOverlapVertex F a j v hv) ≫ J.map (kf (L := L) f) := by
  rw [timedParameter_eq F j b v' hv', timedParameter_eq F j a v hv]
  exact timeParameter_map F f v v' hvertex

/-- The actual used coefficient indices inherit an ordinal operator. -/
def usedOperator (hvertex : orderMap (((codes L).map f).map) v = v') :
    usedDegree F a j v hv ⟶ usedDegree F b j v' hv' :=
  JTPrismRectangle.supportMap
    (JTJointTimedEndpointSupport.timedParameter F a j
      (liftedOverlapVertex F a j v hv))
    (JTJointTimedEndpointSupport.timedParameter F b j
      (liftedOverlapVertex F b j v' hv'))
    ((𝟙 (Δ[0] : SSet.{0}) ⊗ₘ J.map (time.map f))) (kf (L := L) f)
    (timedParameter_map F j f v v' hv hv' hvertex)

include hvertex in
/-- The used ordinal operator commutes with both literal inclusions into the
original coefficient degrees. -/
theorem usedOperator_inclusion :
    usedOperator F j f v v' hv hv' hvertex ≫ usedInclusion F b j v' hv' =
      usedInclusion F a j v hv ≫ kf (L := L) f :=
  JTPrismRectangle.supportMap_inclusion _ _ _ _
    (timedParameter_map F j f v v' hv hv' hvertex)

include hvertex in
/-- Transport preserves the supported parameter on every time simplex. -/
theorem supportedTimedParameter_map :
    (𝟙 (Δ[0] : SSet.{0}) ⊗ₘ J.map (time.map f)) ≫
      supportedTimedParameter F b j (liftedOverlapVertex F b j v' hv') =
      supportedTimedParameter F a j (liftedOverlapVertex F a j v hv) ≫
        J.map (usedOperator F j f v v' hv hv' hvertex) :=
  JTPrismRectangle.supportedParameter_natural _ _ _ _
    (timedParameter_map F j f v v' hv hv' hvertex)

include hvertex in
/-- The degree-zero bead itself is transported by the source operator. -/
theorem sourceBead_map :
    sourceBead F j a v hv ≫ ((codes L).map f).map =
      sourceBead F j b v' hv' := by
  have ha : sourceBead F j a v hv =
      (NecklaceCode.singleIso 0).hom ≫
        pointAt ((codes L).obj a) (ULift.up v) :=
    JTActualSourceJointSupport.vertexBead_eq_sourcePoint F a j v hv
  have hb : sourceBead F j b v' hv' =
      (NecklaceCode.singleIso 0).hom ≫
        pointAt ((codes L).obj b) (ULift.up v') :=
    JTActualSourceJointSupport.vertexBead_eq_sourcePoint F b j v' hv'
  rw [ha, hb, Category.assoc, pointAt_map f v v' hvertex]

include hv hv' hvertex in
/-- The old row-zero coefficient commutes strictly with the original
coefficient operator. -/
theorem oldVertexRow_map :
    std.map (kf (L := L) f) ≫ oldVertexRow (L := L) b v' =
      oldVertexRow (L := L) a v := by
  rw [oldVertexRow_eq_bead F b j v' hv',
    oldVertexRow_eq_bead F a j v hv]
  change std.map (kf (L := L) f) ≫
      JTParametrizedBeadGraph.coefficient (a := b) 0 (sourceBead F j b v' hv') =
    JTParametrizedBeadGraph.coefficient (a := a) 0 (sourceBead F j a v hv)
  rw [← sourceBead_map F j f v v' hv hv' hvertex]
  exact JTParametrizedBeadGraph.coefficient_map f 0 (sourceBead F j a v hv)

end

end DaggerModels.PartII.JTActualSourceJointSupportTransport
