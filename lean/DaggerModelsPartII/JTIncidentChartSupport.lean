import DaggerModelsPartII.JTJointSubdivisionVertexSupport
import DaggerModelsPartII.JTIncidentBeadSupportTransport
import DaggerModelsPartII.JTIncidentBeadImages

/-!
# Whole actual chart support inside the incident union at every chart vertex

The entire actual chart simplex factors through a maximal bead of its full joint
inverse interval or the point piece. Evaluating the same chart vertex proves
incidence at its actual lifted source cut. The complete original timed chart
support therefore includes naturally in that genuine incident support union.
Zero-dimensional charts and arbitrary simplex factors are retained.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTIncidentChartSupport

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row)
open JTTargetJointMarks (Joint)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev J := GroupoidSimplex.parameter

private instance : std.Full :=
  inferInstanceAs (uliftYoneda.{0} (C := SimplexCategory)).Full

private theorem point_piece (T : NecklaceCode) :
    T.pieceι (none : Option T.Bead) =
      SSet.stdSimplex.isTerminalObj₀.from (T.pieces none).toSSet ≫
        pointAt T (ULift.up 0) := by
  apply (cancel_mono T.inclusion).mp
  rw [T.pieceι_inclusion, Category.assoc, pointAt_inclusion]
  apply NatTrans.ext
  funext q x
  obtain ⟨q⟩ := q
  induction q using SimplexCategory.rec with | _ n
  apply SSet.stdSimplex.ext
  intro i
  change x.val i = 0
  have hx := (SSet.stdSimplex.mem_face_iff _ _).mp x.property
  exact Finset.mem_singleton.mp (hx i)

private theorem simplex_incident_factor {T : NecklaceCode} {d : ℕ}
    (g : (Δ[d] : SSet.{0}) ⟶ T.toSSet) (ν : Fin (d + 1))
    (v : T.toSSet.obj (op ⦋0⦌))
    (hv : std.map (SimplexCategory.const ⦋0⦌ ⦋d⦌ ν) ≫ g = SSet.yonedaEquiv.symm v) :
    (∃ B : T.Bead, ∃ u : ⦋d⦌ ⟶ ⦋B.length⦌,
      (T.verticesEquiv v).down ∈ B.interval ∧ std.map u ≫ T.beadSimplex B = g) ∨
    (∃ u : ⦋d⦌ ⟶ ⦋0⦌, std.map u ≫ SSet.yonedaEquiv.symm v = g) := by
  obtain ⟨i, h, hh⟩ := T.simplex_factors_piece g
  cases i with
  | some B =>
      let u := std.preimage (h ≫ B.faceIso.inv)
      have hu : std.map u ≫ T.beadSimplex B = g := by
        rw [show std.map u = _ from std.map_preimage _]
        change (h ≫ B.faceIso.inv) ≫ (B.faceIso.hom ≫ T.beadι B) = _
        rw [Category.assoc, Iso.inv_hom_id_assoc, ← T.pieceι_some]
        exact hh
      left
      refine ⟨B, u, ?_, hu⟩
      rw [← hu, ← Category.assoc, ← std.map_comp, SimplexCategory.const_comp] at hv
      have he := congrArg (fun f : (Δ[0] : SSet.{0}) ⟶ T.toSSet ↦
        T.verticesEquiv (SSet.yonedaEquiv f)) hv
      dsimp only at he
      rw [SSet.yonedaEquiv_comp, SSet.stdSimplex.yonedaEquiv_map,
        Equiv.apply_symm_apply] at he
      change T.verticesEquiv ((T.beadSimplex B).app (op ⦋0⦌)
        (SSet.stdSimplex.obj₀Equiv.symm (u.toOrderHom ν))) = T.verticesEquiv v at he
      rw [B.beadSimplex_vertex] at he
      rw [← congrArg ULift.down he]
      exact Finset.orderEmbOfFin_mem B.interval B.card_interval _
  | none =>
      let u := std.preimage (h ≫ SSet.stdSimplex.isTerminalObj₀.from (T.pieces none).toSSet)
      have hu : std.map u ≫ pointAt T (ULift.up 0) = g := by
        rw [show std.map u = _ from std.map_preimage _, Category.assoc, ← point_piece]
        exact hh
      have hp : pointAt T (ULift.up 0) = SSet.yonedaEquiv.symm v := by
        rw [← hu, ← Category.assoc, ← std.map_comp] at hv
        have hc : SimplexCategory.const ⦋0⦌ ⦋d⦌ ν ≫ u = 𝟙 ⦋0⦌ :=
          Subsingleton.elim _ _
        simpa only [hc, std.map_id, Category.id_comp] using hv
      exact Or.inr ⟨u, hp ▸ hu⟩

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code)

/-- Every ordinal vertex of every actual adjacent-subdivision chart. -/
abbrev Index := JTJointSubdivisionVertexSupport.VertexIndex F j

/-- Its actual original source cut above the fixed joint. -/
abbrev toMarked := JTJointSubdivisionVertexSupport.toMarked F j

private abbrev base := JTJointSubdivisionBeadCharts.base F j
private abbrev D := JTJointSubdivisionBeadNormalization.degrees F j
private abbrev native := JTJointSubdivisionBeadNormalization.inclusion F j
private abbrev marked (p : Index F j) := (toMarked F j).obj p
private abbrev old (p : Index F j) := (base F j).obj p.1
private abbrev gap (p : Index F j) := JTIncidentBeadSupportData.gap F j (marked F j p)
private abbrev gapInclusion (p : Index F j) :=
  JTIncidentBeadSupportData.gapInclusion F j (marked F j p)
private abbrev lifted (p : Index F j) :=
  JTIncidentBeadSupportData.liftedVertex F j (marked F j p)

/-- The whole chart simplex in the actual full inverse interval of its joint. -/
def chartSimplex (p : Index F j) : std.obj ((D F j).obj p.1) ⟶ (gap F j p).toSSet :=
  (singleIso ((D F j).obj p.1).len).inv ≫
    JTJointSubdivisionBeadNormalization.toJointInterval F j p.1

private theorem chart_fac (p : Index F j) :
    chartSimplex F j p ≫ gapInclusion F j p =
      (singleIso ((D F j).obj p.1).len).inv ≫ native F j p.1 := by
  change ((singleIso ((D F j).obj p.1).len).inv ≫
    JTJointSubdivisionBeadNormalization.toJointInterval F j p.1) ≫
      JTTargetIntervalGluing.middleInclusion (F.collapse.app (old F j p)) j = _
  rw [Category.assoc, JTJointSubdivisionBeadNormalization.toJointInterval_fac]

private theorem liftedPoint_fac (p : Index F j) :
    SSet.yonedaEquiv.symm (lifted F j p) ≫ gapInclusion F j p =
      pointAt ((codes L).obj (old F j p))
        (ULift.up (JTJointSubdivisionVertexSupport.cut F j p.1 p.2)) := by
  have h := JTActualSourceJointSupport.vertexBead_eq_sourcePoint F (old F j p) j
    (JTJointSubdivisionVertexSupport.cut F j p.1 p.2)
    (JTJointSubdivisionVertexSupport.cut_at_joint F j p.1 p.2)
  apply (cancel_epi (singleIso 0).hom).mp
  simpa only [JTJointTimedEndpointSupport.vertexBead, Category.assoc] using h

/-- The SAME ordinal chart vertex is precisely the existing actual lifted gap vertex. -/
theorem chart_point (p : Index F j) :
    std.map (SimplexCategory.const ⦋0⦌ ((D F j).obj p.1) p.2) ≫ chartSimplex F j p =
      SSet.yonedaEquiv.symm (lifted F j p) := by
  haveI : Mono (gapInclusion F j p) := by
    dsimp only [gapInclusion, JTIncidentBeadSupportData.gapInclusion,
      JTTargetIntervalGluing.middleInclusion, JTTargetIntervalPullback.sourceInclusion]
    infer_instance
  apply (cancel_mono (gapInclusion F j p)).mp
  rw [Category.assoc, chart_fac, liftedPoint_fac]
  exact (JTJointSubdivisionVertexSupport.point_factor F j p.1 p.2).symm

private theorem bead_horizontal (p : Index F j) (B : (gap F j p).Bead)
    (u : ((D F j).obj p.1) ⟶ ⦋B.length⦌)
    (h : std.map u ≫ (gap F j p).beadSimplex B = chartSimplex F j p) :
    (singleIso ((D F j).obj p.1).len).inv ≫ native F j p.1 ≫
        ((codes L).map (𝟙 (old F j p))).map =
      std.map u ≫ (singleIso B.length).inv ≫
        JTIncidentBeadSupportData.beadNative F j (marked F j p) B := by
  rw [(codes L).map_id]
  change (singleIso ((D F j).obj p.1).len).inv ≫ native F j p.1 ≫ 𝟙 _ = _
  rw [Category.comp_id]
  have hh := congrArg (fun f ↦ f ≫ gapInclusion F j p) h
  dsimp only at hh
  rw [Category.assoc, chart_fac] at hh
  simpa only [JTIncidentBeadSupportData.beadNative, JTIncidentBeadSupportData.beadIntoGap,
    Category.assoc, Iso.inv_hom_id_assoc] using hh.symm

private theorem point_horizontal (p : Index F j) (u : ((D F j).obj p.1) ⟶ ⦋0⦌)
    (h : std.map u ≫ SSet.yonedaEquiv.symm (lifted F j p) = chartSimplex F j p) :
    (singleIso ((D F j).obj p.1).len).inv ≫ native F j p.1 ≫
        ((codes L).map (𝟙 (old F j p))).map =
      std.map u ≫ (singleIso 0).inv ≫
        JTIncidentBeadSupportData.vertexNative F j (marked F j p) := by
  rw [(codes L).map_id]
  change (singleIso ((D F j).obj p.1).len).inv ≫ native F j p.1 ≫ 𝟙 _ = _
  rw [Category.comp_id]
  have hh := congrArg (fun f ↦ f ≫ gapInclusion F j p) h
  dsimp only at hh
  rw [Category.assoc, chart_fac] at hh
  simpa only [JTIncidentBeadSupportData.vertexNative, JTJointTimedEndpointSupport.vertexBead,
    Category.assoc, Iso.inv_hom_id_assoc] using hh.symm

private theorem support_range_le (a : A) {d e : ℕ}
    (i : (single d).toSSet ⟶ ((codes L).obj a).toSSet)
    (i' : (single e).toSSet ⟶ ((codes L).obj a).toSSet) (u : ⦋d⦌ ⟶ ⦋e⦌)
    (h : (singleIso d).inv ≫ i ≫ ((codes L).map (𝟙 a)).map =
      std.map u ≫ (singleIso e).inv ≫ i') :
    SSet.Subcomplex.range (std.map (JTParametrizedBeadGraph.fullBeadSupportInclusion F a d i)) ≤
      SSet.Subcomplex.range (std.map
        (JTParametrizedBeadGraph.fullBeadSupportInclusion F a e i')) := by
  let σ := JTParametrizedBeadGraph.fullBeadSupportMap F (𝟙 a) (i := i) (i' := i') u h
  have hs := JTPrismRectangle.supportMap_inclusion
    (JTParametrizedBeadGraph.fullBeadParameter F a d i)
    (JTParametrizedBeadGraph.fullBeadParameter F a e i')
    (std.map u ⊗ₘ J.map (time.map (𝟙 a)))
    ((JTJointRelativeGraphFamily.coefficient (L := L)).map (𝟙 a))
    (JTParametrizedBeadGraph.fullBeadParameter_map F (𝟙 a) (i := i) (i' := i') u h)
  have he : σ ≫ JTParametrizedBeadGraph.fullBeadSupportInclusion F a e i' =
      JTParametrizedBeadGraph.fullBeadSupportInclusion F a d i :=
    hs.trans ((congrArg (fun t ↦
      JTParametrizedBeadGraph.fullBeadSupportInclusion F a d i ≫ t)
        ((JTJointRelativeGraphFamily.coefficient (L := L)).map_id a)).trans (Category.comp_id _))
  rw [← he, std.map_comp]
  exact Subfunctor.range_comp_le _ _

/-- The WHOLE actual timed chart face lies in the incident union at this actual chart vertex. -/
theorem face_le_support (p : Index F j) :
    SSet.Subcomplex.range (std.map (JTJointSubdivisionVertexSupport.beadInclusion F j p.1)) ≤
      JTIncidentBeadSupportData.support F j (marked F j p) := by
  rcases simplex_incident_factor (chartSimplex F j p) p.2 (lifted F j p)
      (chart_point F j p) with ⟨B, u, hB, h⟩ | ⟨u, h⟩
  · exact (support_range_le F (old F j p) (native F j p.1)
      (JTIncidentBeadSupportData.beadNative F j (marked F j p) B) u
      (bead_horizontal F j p B u h)).trans
        (JTIncidentBeadSupportData.beadFace_le_support F j (marked F j p) B hB)
  · exact (support_range_le F (old F j p) (native F j p.1)
      (JTIncidentBeadSupportData.vertexNative F j (marked F j p)) u
      (point_horizontal F j p u h)).trans
        (JTIncidentBeadSupportData.vertexFace_le_support F j (marked F j p))

/-- The literal full timed chart support at every actual chart vertex. -/
def chartSupports : Index F j ⥤ SimplexCategory where
  obj p := JTJointSubdivisionVertexSupport.beadSupport F j p.1
  map f := JTJointSubdivisionVertexSupport.beadSupportMap F j f.val
  map_id p := by
    haveI : Mono (JTJointSubdivisionVertexSupport.beadInclusion F j p.1) :=
      JTRowGraphParameterSupport.inclusion_mono _
    apply (cancel_mono (JTJointSubdivisionVertexSupport.beadInclusion F j p.1)).mp
    change JTJointSubdivisionVertexSupport.beadSupportMap F j (𝟙 p.1) ≫
      JTJointSubdivisionVertexSupport.beadInclusion F j p.1 =
        𝟙 _ ≫ JTJointSubdivisionVertexSupport.beadInclusion F j p.1
    rw [JTJointSubdivisionVertexSupport.beadSupportMap_inclusion,
      (base F j).map_id, Category.id_comp]
    exact (congrArg (fun u ↦ JTJointSubdivisionVertexSupport.beadInclusion F j p.1 ≫ u)
      ((JTJointRelativeGraphFamily.coefficient (L := L)).map_id (old F j p))).trans
        (Category.comp_id _)
  map_comp {p q r} f g := by
    haveI : Mono (JTJointSubdivisionVertexSupport.beadInclusion F j r.1) :=
      JTRowGraphParameterSupport.inclusion_mono _
    apply (cancel_mono (JTJointSubdivisionVertexSupport.beadInclusion F j r.1)).mp
    change JTJointSubdivisionVertexSupport.beadSupportMap F j (f.val ≫ g.val) ≫
      JTJointSubdivisionVertexSupport.beadInclusion F j r.1 =
        (JTJointSubdivisionVertexSupport.beadSupportMap F j f.val ≫
          JTJointSubdivisionVertexSupport.beadSupportMap F j g.val) ≫
            JTJointSubdivisionVertexSupport.beadInclusion F j r.1
    simp only [Category.assoc, JTJointSubdivisionVertexSupport.beadSupportMap_inclusion]
    rw [(base F j).map_comp, (JTJointRelativeGraphFamily.coefficient (L := L)).map_comp]
    conv_rhs => rw [← Category.assoc, JTJointSubdivisionVertexSupport.beadSupportMap_inclusion]
    exact (Category.assoc (JTJointSubdivisionVertexSupport.beadInclusion F j p.1)
      ((JTJointRelativeGraphFamily.coefficient (L := L)).map ((base F j).map f.val))
      ((JTJointRelativeGraphFamily.coefficient (L := L)).map ((base F j).map g.val))).symm

/-- The unchanged original coefficient diagram at the actual chart vertices. -/
abbrev oldDegrees := toMarked F j ⋙ JTExactlyMarkedSourceDiagram.degrees F j

/-- The full chart support's literal old coefficient inclusion. -/
def chartInclusion : chartSupports F j ⟶ oldDegrees F j where
  app p := JTJointSubdivisionVertexSupport.beadInclusion F j p.1
  naturality _ _ f := JTJointSubdivisionVertexSupport.beadSupportMap_inclusion F j f.val

/-- The genuine incident union at the same actual original source cut. -/
abbrev incidentSupports := toMarked F j ⋙ JTIncidentBeadSupportTransport.diagram F j

/-- Its unchanged original coefficient inclusion. -/
abbrev incidentInclusion :=
  Functor.whiskerLeft (toMarked F j) (JTIncidentBeadSupportTransport.inclusion F j)

private def toIncidentApp (p : Index F j) :
    std.obj ((chartSupports F j).obj p) ⟶ (incidentSupports F j).obj p :=
  (JTIncidentBeadSupportData.support F j (marked F j p)).lift
    (std.map ((chartInclusion F j).app p)) (face_le_support F j p)

private theorem toIncidentApp_fac (p : Index F j) :
    toIncidentApp F j p ≫ (incidentInclusion F j).app p =
      std.map ((chartInclusion F j).app p) := rfl

/-- Canonical inclusion of each entire timed chart support in the actual incident union. -/
def toIncident : chartSupports F j ⋙ std ⟶ incidentSupports F j where
  app := toIncidentApp F j
  naturality {p q} f := by
    haveI : Mono ((incidentInclusion F j).app q) := by
      change Mono (JTIncidentBeadSupportData.support F j (marked F j q)).ι
      infer_instance
    apply (cancel_mono ((incidentInclusion F j).app q)).mp
    change (std.map ((chartSupports F j).map f) ≫ toIncidentApp F j q) ≫
      (incidentInclusion F j).app q =
        (toIncidentApp F j p ≫ (incidentSupports F j).map f) ≫
          (incidentInclusion F j).app q
    rw [Category.assoc, toIncidentApp_fac, Category.assoc,
      (incidentInclusion F j).naturality f, ← Category.assoc, toIncidentApp_fac]
    simpa only [std.map_comp] using congrArg std.map ((chartInclusion F j).naturality f)

/-- The support comparison retains the exact original coefficient inclusion in every degree. -/
theorem toIncident_fac : toIncident F j ≫ incidentInclusion F j =
    Functor.whiskerRight (chartInclusion F j) std := by
  apply NatTrans.ext
  funext p
  rfl

end
end DaggerModels.PartII.JTIncidentChartSupport
