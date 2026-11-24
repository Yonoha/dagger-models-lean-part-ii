import DaggerModelsPartII.JTJointSubdivisionBeadNormalization
import DaggerModelsPartII.JTActualSourceJointSupportTransport

/-!
The full timed support at every actual vertex of an adjacent-subdivision bead
includes in that bead's full timed support. The point-to-bead operator is an
arbitrary simplex vertex map, not an endpoint-preserving necklace map.
All source cuts, support factorizations, row equations and time parameters
derive from the original full family and its actual image chart.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTJointSubdivisionVertexSupport

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row vertexPoint)
open JTTargetJointMarks (Joint)
open JTJointSubdivisionBeadCharts (Index base)
open JTJointSubdivisionBeadNormalization (degrees inclusion inclusion_joint toJointInterval)
open JTParametrizedBeadGraph (fullBeadSupport fullBeadSupportInclusion fullBeadParameter)
open ReversalDiscreteFreeColimits (discreteFree)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev pre (W : Source) {X Y : SSet.{0}} (g : X ⟶ Y) :=
  diagramMappingPrecomp (discreteFree.map g) W

private theorem constant_at_point (W : Source) (z : Vertex W) (T : NecklaceCode)
    (k : SimplexCategory) (v : (Δ[0] : SSet.{0}) ⟶ T.toSSet) :
    JTConstantOrderedLabel.constantCoefficient W z T k ≫ pre W v =
      term (std.obj k) ≫ OrderedNecklaceVertexPoints.zeroPoint W z := by
  have h : v ≫ term T.toSSet = 𝟙 (Δ[0] : SSet.{0}) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  simp only [JTConstantOrderedLabel.constantCoefficient, pre, Category.assoc,
    ← diagramMappingPrecomp_comp, ← discreteFree.map_comp, h, discreteFree.map_id,
    diagramMappingPrecomp_id, Category.comp_id]

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time) (j : Joint Q.code)

private theorem coefficient_supported (a : A) (n : ℕ)
    (r : (single n).toSSet ⟶
      (JTTargetIntervalPullback.sourceInterval (F.collapse.app a) j j le_rfl).toSSet)
    (i : (single n).toSSet ⟶ ((codes L).obj a).toSSet)
    (hi : r ≫ JTTargetIntervalGluing.middleInclusion (F.collapse.app a) j = i) :
    std.map (fullBeadSupportInclusion F a n i) ≫ SSet.yonedaEquiv.symm
        (JTParametrizedBeadGraph.beadLabel (a := a) n i) =
      JTConstantOrderedLabel.constantCoefficient W
        (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j) (single n)
        (fullBeadSupport F a n i) := by
  subst i
  exact JTJointBeadSupportedNormalization.coefficient_onSupport F a n j r

private abbrev old (p : Index F j) := (base F j).obj p
private abbrev d (p : Index F j) := ((degrees F j).obj p).len
private abbrev T (p : Index F j) := (codes L).obj (old F j p)
private abbrev K (p : Index F j) :=
  (JTJointRelativeGraphFamily.coefficient (L := L)).obj (old F j p)

/-- The genuine original source cut named by the actual chart vertex. -/
def cut (p : Index F j) (ν : Fin (d F j p + 1)) : Fin ((T F j p).len + 1) :=
  orderMap (inclusion F j p) ν

/-- Every such original source cut lies over the same fixed target joint. -/
theorem cut_at_joint (p : Index F j) (ν : Fin (d F j p + 1)) :
    orderMap (F.collapse.app (old F j p)).map (cut F j p ν) = j.val := by
  rw [cut, ← orderMap_comp_apply, inclusion_joint]
  change orderMap (term (single (d F j p)).toSSet ≫ pointAt Q.code (ULift.up j.val)) ν = _
  change (Q.code.verticesEquiv
    ((pointAt Q.code (ULift.up j.val)).app (op ⦋0⦌) _)).down = j.val
  unfold pointAt
  rw [pointAt_vertex_apply, Q.code.verticesEquiv.apply_symm_apply]

/-- The full old coefficient support used by the whole native bead and all original time. -/
abbrev beadSupport (p : Index F j) :=
  fullBeadSupport F (old F j p) (d F j p) (inclusion F j p)

/-- Its literal inclusion in the original coefficient ordinal. -/
abbrev beadInclusion (p : Index F j) :=
  fullBeadSupportInclusion F (old F j p) (d F j p) (inclusion F j p)

/-- Use exactly the existing actual-source-vertex timed support, with no new support choice. -/
abbrev vertexSupport (p : Index F j) (ν : Fin (d F j p + 1)) :=
  JTActualSourceJointSupport.usedDegree F (old F j p) j
    (cut F j p ν) (cut_at_joint F j p ν)

/-- The original coefficient inclusion of that existing vertex support. -/
abbrev vertexInclusion (p : Index F j) (ν : Fin (d F j p + 1)) :=
  JTActualSourceJointSupport.usedInclusion F (old F j p) j
    (cut F j p ν) (cut_at_joint F j p ν)

private abbrev vertexBead (p : Index F j) (ν : Fin (d F j p + 1)) :=
  JTJointTimedEndpointSupport.vertexBead F (old F j p) j
      (JTActualSourceJointSupport.liftedOverlapVertex F (old F j p) j
        (cut F j p ν) (cut_at_joint F j p ν)) ≫
    JTTargetIntervalGluing.middleInclusion (F.collapse.app (old F j p)) j

private abbrev vertexOperator (p : Index F j) (ν : Fin (d F j p + 1)) :=
  SimplexCategory.const ⦋0⦌ ⦋d F j p⦌ ν

/-- The actual old point map is the selected simplex vertex followed by the full chart. -/
theorem point_factor (p : Index F j) (ν : Fin (d F j p + 1)) :
    pointAt (T F j p) (ULift.up (cut F j p ν)) =
      std.map (vertexOperator F j p ν) ≫ (singleIso (d F j p)).inv ≫ inclusion F j p := by
  have h := JTNativeRowLabel.nativeVertex (d F j p) ν
  change pointAt (single (d F j p)) (ULift.up ν) ≫ (singleIso (d F j p)).hom =
    std.map (vertexOperator F j p ν) at h
  rw [← h, Category.assoc, Iso.hom_inv_id_assoc, pointAt_comp]
  rfl

private theorem vertex_horizontal (p : Index F j) (ν : Fin (d F j p + 1)) :
    (singleIso 0).inv ≫ vertexBead F j p ν ≫ ((codes L).map (𝟙 (old F j p))).map =
      std.map (vertexOperator F j p ν) ≫ (singleIso (d F j p)).inv ≫ inclusion F j p := by
  have hi : vertexBead F j p ν = (singleIso 0).hom ≫
      pointAt (T F j p) (ULift.up (cut F j p ν)) :=
    JTActualSourceJointSupport.vertexBead_eq_sourcePoint F (old F j p) j
      (cut F j p ν) (cut_at_joint F j p ν)
  rw [(codes L).map_id]
  change (singleIso 0).inv ≫ vertexBead F j p ν ≫ 𝟙 _ = _
  rw [Category.comp_id, hi, Iso.inv_hom_id_assoc]
  exact point_factor F j p ν

/-- The actual point support includes in the full bead support through an arbitrary vertex map. -/
def vertexToBead (p : Index F j) (ν : Fin (d F j p + 1)) :
    vertexSupport F j p ν ⟶ beadSupport F j p :=
  JTParametrizedBeadGraph.fullBeadSupportMap F (𝟙 (old F j p))
    (i := vertexBead F j p ν) (i' := inclusion F j p)
    (vertexOperator F j p ν) (vertex_horizontal F j p ν)

/-- Both actual supports have exactly the same inclusion into the ORIGINAL coefficient. -/
theorem vertexToBead_inclusion (p : Index F j) (ν : Fin (d F j p + 1)) :
    vertexToBead F j p ν ≫ beadInclusion F j p = vertexInclusion F j p ν := by
  have h := JTPrismRectangle.supportMap_inclusion
    (fullBeadParameter F (old F j p) 0 (vertexBead F j p ν))
    (fullBeadParameter F (old F j p) (d F j p) (inclusion F j p))
    (std.map (vertexOperator F j p ν) ⊗ₘ J.map (time.map (𝟙 (old F j p))))
    ((JTJointRelativeGraphFamily.coefficient (L := L)).map (𝟙 (old F j p)))
    (JTParametrizedBeadGraph.fullBeadParameter_map F (𝟙 (old F j p))
      (i := vertexBead F j p ν) (i' := inclusion F j p)
      (vertexOperator F j p ν) (vertex_horizontal F j p ν))
  change vertexToBead F j p ν ≫ beadInclusion F j p = vertexInclusion F j p ν ≫
    (JTJointRelativeGraphFamily.coefficient (L := L)).map (𝟙 (old F j p)) at h
  rw [(JTJointRelativeGraphFamily.coefficient (L := L)).map_id, Category.comp_id] at h
  exact h

/-- The actual support comparison is monic, since its composite is the old monic inclusion. -/
theorem vertexToBead_mono (p : Index F j) (ν : Fin (d F j p + 1)) :
    Mono (vertexToBead F j p ν) := by
  haveI : Mono (vertexInclusion F j p ν) :=
    JTActualSourceJointSupport.usedInclusion_mono F (old F j p) j
      (cut F j p ν) (cut_at_joint F j p ν)
  haveI : Mono (vertexToBead F j p ν ≫ beadInclusion F j p) := by
    rw [vertexToBead_inclusion]
    infer_instance
  exact mono_of_mono _ (beadInclusion F j p)

/-- The actual old vertex row is the same horizontal face of the full original bead coefficient. -/
theorem row_face (p : Index F j) (ν : Fin (d F j p + 1)) :
    JTActualSourceJointSupport.oldVertexRow (L := L) (old F j p) (cut F j p ν) =
      JTParametrizedBeadGraph.coefficient (a := old F j p) (d F j p) (inclusion F j p) ≫
        JTMixedGraphEndpointLifts.rowVertex W ⦋d F j p⦌ ν := by
  rw [JTActualSourceJointSupport.oldVertexRow_eq_bead F (old F j p) j
    (cut F j p ν) (cut_at_joint F j p ν)]
  apply JTParametrizedBeadGraph.coefficient_horizontal
  have h := vertex_horizontal F j p ν
  rw [(codes L).map_id] at h
  change (singleIso 0).inv ≫ vertexBead F j p ν ≫ 𝟙 _ = _ at h
  rw [Category.comp_id] at h
  exact h

/-- The same actual row is stationary on the WHOLE bead support, not only its vertex support. -/
theorem row_on_beadSupport (p : Index F j) (ν : Fin (d F j p + 1)) :
    std.map (beadInclusion F j p) ≫
        JTActualSourceJointSupport.oldVertexRow (L := L) (old F j p) (cut F j p ν) =
      term (std.obj (beadSupport F j p)) ≫
        vertexPoint W (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j) := by
  let z := JTParametrizedBeadGraph.jointCoefficient (Q := Q) j
  let c := SSet.yonedaEquiv.symm
    (JTParametrizedBeadGraph.beadLabel (a := old F j p) (d F j p) (inclusion F j p))
  have hc : std.map (beadInclusion F j p) ≫ c =
      JTConstantOrderedLabel.constantCoefficient W z (single (d F j p))
        (beadSupport F j p) := by
    exact coefficient_supported F j (old F j p) (d F j p) (toJointInterval F j p)
      (inclusion F j p) (JTJointSubdivisionBeadNormalization.toJointInterval_fac F j p)
  have hr : JTParametrizedBeadGraph.coefficient (a := old F j p)
        (d F j p) (inclusion F j p) ≫ JTNativeRowLabel.labelFromRow W (d F j p) = c := by
    apply SSet.yonedaEquiv.injective
    simpa only [c, Equiv.apply_symm_apply] using
      JTParametrizedBeadGraph.coefficient_label (a := old F j p)
        (d F j p) (inclusion F j p)
  haveI : Mono (TwoBeadEndpointLabel.jointLabelFromRow W) := by
    change Mono (OrderedSimplexEndpointFiber.freeSimplexRowIso W 0).inv
    infer_instance
  apply (cancel_mono (TwoBeadEndpointLabel.jointLabelFromRow W)).mp
  calc
    _ = (std.map (beadInclusion F j p) ≫ c) ≫
        pre W (pointAt (single (d F j p)) (ULift.up ν)) := by
      rw [row_face]
      have h := congrArg (fun q ↦ std.map (beadInclusion F j p) ≫ q ≫
        pre W (pointAt (single (d F j p)) (ULift.up ν))) hr
      simpa only [Category.assoc, JTNativeRowLabel.labelFromRow_vertex] using h
    _ = JTConstantOrderedLabel.constantCoefficient W z (single (d F j p))
        (beadSupport F j p) ≫ pre W (pointAt (single (d F j p)) (ULift.up ν)) := by
      rw [hc]
    _ = term (std.obj (beadSupport F j p)) ≫
        OrderedNecklaceVertexPoints.zeroPoint W z := constant_at_point _ _ _ _ _
    _ = _ := by rw [Category.assoc, TwoBeadEndpointLabel.jointLabelFromRow_vertex]

/-- The full supported original-time parameter at the vertex. -/
abbrev vertexParameter (p : Index F j) (ν : Fin (d F j p + 1)) :=
  JTJointTimedEndpointSupport.supportedTimedParameter F (old F j p) j
    (JTActualSourceJointSupport.liftedOverlapVertex F (old F j p) j
      (cut F j p ν) (cut_at_joint F j p ν))

/-- The supported parameter of the whole actual bead prism. -/
abbrev beadParameter (p : Index F j) :=
  JTPrismRectangle.supportedParameter
    (fullBeadParameter F (old F j p) (d F j p) (inclusion F j p))

/-- Restricting the whole bead parameter to this vertex retains every original time simplex. -/
theorem parameter_square (p : Index F j) (ν : Fin (d F j p + 1)) :
    (std.map (vertexOperator F j p ν) ⊗ₘ 𝟙 (J.obj (time.obj (old F j p)))) ≫
        beadParameter F j p =
      vertexParameter F j p ν ≫ J.map (vertexToBead F j p ν) := by
  have h := JTParametrizedBeadGraph.supportedFullBeadParameter_map F
    (𝟙 (old F j p)) (i := vertexBead F j p ν) (i' := inclusion F j p)
    (vertexOperator F j p ν) (vertex_horizontal F j p ν)
  change (std.map (vertexOperator F j p ν) ⊗ₘ J.map (time.map (𝟙 (old F j p)))) ≫
    beadParameter F j p = vertexParameter F j p ν ≫ J.map (vertexToBead F j p ν) at h
  rw [time.map_id, J.map_id] at h
  exact h

/-- The resulting supported vertex parameter factors through the unchanged old coefficient. -/
theorem parameter_original (p : Index F j) (ν : Fin (d F j p + 1)) :
    (vertexParameter F j p ν ≫ J.map (vertexToBead F j p ν)) ≫
        J.map (beadInclusion F j p) =
      JTActualSourceJointSupport.timeParameter F (old F j p) (cut F j p ν) := by
  rw [Category.assoc, ← J.map_comp, vertexToBead_inclusion]
  exact JTActualSourceJointSupport.timeParameter_factor F (old F j p) j
    (cut F j p ν) (cut_at_joint F j p ν)

/-- The canonical concrete simplex functor gives the actual chart-and-vertex source. -/
abbrev VertexIndex := ((degrees F j) ⋙ forget SimplexCategory).Elements

/-- Forget the named ordinal vertex while retaining its actual original chart arrow. -/
abbrev toCharts : VertexIndex F j ⥤ Index F j :=
  CategoryOfElements.π ((degrees F j) ⋙ forget SimplexCategory)

/-- All original chart maps carry the named source vertex to its exact actual image. -/
theorem cut_natural {p q : VertexIndex F j} (f : p ⟶ q) :
    orderMap ((codes L).map ((base F j).map f.val)).map (cut F j p.1 p.2) =
      cut F j q.1 q.2 := by
  have h := congrArg (fun u : (single (d F j p.1)).toSSet ⟶ (T F j q.1).toSSet ↦
    orderMap u (p.2 : Fin (d F j p.1 + 1)))
    (JTJointSubdivisionBeadNormalization.inclusion_natural F j f.val)
  simp only [orderMap_comp_apply] at h
  have hv : orderMap ((JTJointSubdivisionBeadCharts.singleNative F j).map f.val).map p.2 =
      q.2 := f.property
  exact h.symm.trans (congrArg (fun v : Fin (d F j q.1 + 1) ↦
    orderMap (inclusion F j q.1) v) hv)

/-- The actual vertex source maps to the existing exactly marked source without a new cut choice. -/
def toMarked : VertexIndex F j ⥤ JTExactlyMarkedSourceDiagram.Index F j where
  obj p := ⟨old F j p.1, ⟨cut F j p.1 p.2, cut_at_joint F j p.1 p.2⟩⟩
  map f := ⟨(base F j).map f.val, Subtype.ext (cut_natural F j f)⟩
  map_id p := by apply CategoryOfElements.ext; exact (base F j).map_id p.1
  map_comp f g := by apply CategoryOfElements.ext; exact (base F j).map_comp f.val g.val

private theorem chart_native_natural {p q : Index F j} (f : p ⟶ q) :
    (singleIso (d F j p)).inv ≫ inclusion F j p ≫ ((codes L).map ((base F j).map f)).map =
      std.map ((degrees F j).map f) ≫ (singleIso (d F j q)).inv ≫ inclusion F j q := by
  have h := JTJointSubdivisionBeadNormalization.native_natural F j f
  simpa only [JTJointSubdivisionBeadNormalization.toJointInterval_fac] using h

/-- The full bead support operator of the original chart map and all original time. -/
def beadSupportMap {p q : Index F j} (f : p ⟶ q) :
    beadSupport F j p ⟶ beadSupport F j q :=
  JTParametrizedBeadGraph.fullBeadSupportMap F ((base F j).map f)
    ((degrees F j).map f) (chart_native_natural F j f)

/-- This actual support operator retains the original coefficient operator. -/
theorem beadSupportMap_inclusion {p q : Index F j} (f : p ⟶ q) :
    beadSupportMap F j f ≫ beadInclusion F j q = beadInclusion F j p ≫
      (JTJointRelativeGraphFamily.coefficient (L := L)).map ((base F j).map f) :=
  JTPrismRectangle.supportMap_inclusion _ _ _ _
    (JTParametrizedBeadGraph.fullBeadParameter_map F ((base F j).map f)
      ((degrees F j).map f) (chart_native_natural F j f))

/-- Actual vertex-support inclusions commute with every chart-and-vertex operator. -/
theorem vertexToBead_natural {p q : VertexIndex F j} (f : p ⟶ q) :
    JTActualSourceJointSupportTransport.usedOperator F j ((base F j).map f.val)
        (cut F j p.1 p.2) (cut F j q.1 q.2)
        (cut_at_joint F j p.1 p.2) (cut_at_joint F j q.1 q.2) (cut_natural F j f) ≫
      vertexToBead F j q.1 q.2 =
    vertexToBead F j p.1 p.2 ≫ beadSupportMap F j f.val := by
  haveI : Mono (beadInclusion F j q.1) := JTRowGraphParameterSupport.inclusion_mono _
  apply (cancel_mono (beadInclusion F j q.1)).mp
  simp only [Category.assoc, vertexToBead_inclusion, beadSupportMap_inclusion]
  rw [← Category.assoc, vertexToBead_inclusion]
  exact JTActualSourceJointSupportTransport.usedOperator_inclusion F j
    ((base F j).map f.val) (cut F j p.1 p.2) (cut F j q.1 q.2)
    (cut_at_joint F j p.1 p.2) (cut_at_joint F j q.1 q.2) (cut_natural F j f)

end
end DaggerModels.PartII.JTJointSubdivisionVertexSupport
