import DaggerModelsPartII.JTExactlyMarkedSourceDiagram
import DaggerModelsPartII.JTJointBeadSupportedNormalization
import ChosenNecklaceBeadCoordinates

/-!
# Incident bead supports in the actual joint inverse interval

The support is a union of genuine coefficient subcomplexes. It retains the
actual vertex face, including the case of a point inverse interval, and the
full timed faces of all maximal beads incident at that vertex. The original
vertex row is stationary on this union. No transport or weakness of the union
is asserted here.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTIncidentBeadSupportData

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row vertexPoint)
open JTTargetJointMarks (Joint)
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

/-- The original source with an exactly transported vertex above the fixed joint. -/
abbrev Index := JTExactlyMarkedSourceDiagram.Index F j

/-- The actual full inverse interval of the joint. -/
abbrev gap (p : Index F j) :=
  JTTargetIntervalPullback.sourceInterval (F.collapse.app p.1) j j le_rfl

/-- The original inclusion of this full inverse interval. -/
abbrev gapInclusion (p : Index F j) :=
  JTTargetIntervalGluing.middleInclusion (F.collapse.app p.1) j

/-- The existing actual lift of the selected original vertex. -/
abbrev liftedVertex (p : Index F j) :=
  JTActualSourceJointSupport.liftedOverlapVertex F p.1 j p.2.val p.2.property

/-- Its ordinal coordinate in the actual inverse interval. -/
def gapCoordinate (p : Index F j) : Fin ((gap F j p).len + 1) :=
  ((gap F j p).verticesEquiv (liftedVertex F j p)).down

/-- Incidence refers to maximal beads of the clipped actual inverse interval. -/
def Incident (p : Index F j) (B : (gap F j p).Bead) : Prop :=
  gapCoordinate F j p ∈ B.interval

/-- The simplex presentation of a maximal bead of the actual gap. -/
def beadIntoGap (p : Index F j) (B : (gap F j p).Bead) :=
  (singleIso B.length).hom ≫ (gap F j p).beadSimplex B

/-- Its exact native map into the original source necklace. -/
def beadNative (p : Index F j) (B : (gap F j p).Bead) :=
  beadIntoGap F j p B ≫ gapInclusion F j p

/-- The existing actual timed vertex support. -/
abbrev vertexSupport (p : Index F j) := (JTExactlyMarkedSourceDiagram.supports F j).obj p

/-- Its original coefficient inclusion. -/
abbrev vertexInclusion (p : Index F j) := (JTExactlyMarkedSourceDiagram.incl F j).app p

/-- The full original time support of the entire incident bead. -/
abbrev beadSupport (p : Index F j) (B : (gap F j p).Bead) :=
  fullBeadSupport F p.1 B.length (beadNative F j p B)

/-- Its original coefficient inclusion. -/
abbrev beadInclusion (p : Index F j) (B : (gap F j p).Bead) :=
  fullBeadSupportInclusion F p.1 B.length (beadNative F j p B)

/-- The simplex coordinate of the incident vertex inside this bead. -/
def beadCoordinate (p : Index F j) (B : (gap F j p).Bead) (h : Incident F j p B) :
    Fin (B.length + 1) :=
  (B.interval.orderIsoOfFin B.card_interval).symm ⟨gapCoordinate F j p, h⟩

theorem beadCoordinate_embedding (p : Index F j) (B : (gap F j p).Bead)
    (h : Incident F j p B) : B.embedding (beadCoordinate F j p B h) =
      gapCoordinate F j p :=
  congrArg Subtype.val ((B.interval.orderIsoOfFin B.card_interval).apply_symm_apply _)

/-- The arbitrary simplex vertex operator selecting the incident point. -/
abbrev vertexOperator (p : Index F j) (B : (gap F j p).Bead)
    (h : Incident F j p B) :=
  SimplexCategory.const ⦋0⦌ ⦋B.length⦌ (beadCoordinate F j p B h)

/-- The original native degree-zero map at the selected actual source vertex. -/
abbrev vertexNative (p : Index F j) :=
  JTJointTimedEndpointSupport.vertexBead F p.1 j (liftedVertex F j p) ≫ gapInclusion F j p

/-- The actual point factors through every incident bead, with its precise simplex vertex. -/
theorem point_factor (p : Index F j) (B : (gap F j p).Bead) (h : Incident F j p B) :
    SSet.yonedaEquiv.symm (liftedVertex F j p) =
      std.map (vertexOperator F j p B h) ≫ (gap F j p).beadSimplex B := by
  apply SSet.yonedaEquiv.injective
  apply (gap F j p).verticesEquiv.injective
  rw [Equiv.apply_symm_apply, SSet.yonedaEquiv_comp, SSet.stdSimplex.yonedaEquiv_map]
  change (gap F j p).verticesEquiv (liftedVertex F j p) =
    (gap F j p).verticesEquiv ((gap F j p).beadSimplex B |>.app (op ⦋0⦌)
      (SSet.stdSimplex.obj₀Equiv.symm (beadCoordinate F j p B h)))
  rw [B.beadSimplex_vertex, beadCoordinate_embedding]
  rfl

private theorem vertex_horizontal (p : Index F j) (B : (gap F j p).Bead)
    (h : Incident F j p B) :
    (singleIso 0).inv ≫ vertexNative F j p ≫ ((codes L).map (𝟙 p.1)).map =
      std.map (vertexOperator F j p B h) ≫ (singleIso B.length).inv ≫
        beadNative F j p B := by
  rw [(codes L).map_id]
  change (singleIso 0).inv ≫ vertexNative F j p ≫ 𝟙 _ = _
  rw [Category.comp_id]
  change (singleIso 0).inv ≫
    ((singleIso 0).hom ≫ SSet.yonedaEquiv.symm (liftedVertex F j p)) ≫
      gapInclusion F j p = _
  simp only [beadNative, beadIntoGap, Category.assoc, Iso.inv_hom_id_assoc]
  rw [point_factor F j p B h, Category.assoc]

/-- The actual vertex support includes into every incident bead's full timed support. -/
def vertexToBead (p : Index F j) (B : (gap F j p).Bead) (h : Incident F j p B) :
    vertexSupport F j p ⟶ beadSupport F j p B :=
  JTParametrizedBeadGraph.fullBeadSupportMap F (𝟙 p.1)
    (i := vertexNative F j p) (i' := beadNative F j p B)
    (vertexOperator F j p B h) (vertex_horizontal F j p B h)

/-- This comparison has its literal inclusion into the original coefficient ordinal. -/
theorem vertexToBead_inclusion (p : Index F j) (B : (gap F j p).Bead)
    (h : Incident F j p B) :
    vertexToBead F j p B h ≫ beadInclusion F j p B = vertexInclusion F j p := by
  have hh := JTPrismRectangle.supportMap_inclusion
    (fullBeadParameter F p.1 0 (vertexNative F j p))
    (fullBeadParameter F p.1 B.length (beadNative F j p B))
    (std.map (vertexOperator F j p B h) ⊗ₘ J.map (time.map (𝟙 p.1)))
    ((JTJointRelativeGraphFamily.coefficient (L := L)).map (𝟙 p.1))
    (JTParametrizedBeadGraph.fullBeadParameter_map F (𝟙 p.1)
      (i := vertexNative F j p) (i' := beadNative F j p B)
      (vertexOperator F j p B h) (vertex_horizontal F j p B h))
  change vertexToBead F j p B h ≫ beadInclusion F j p B = vertexInclusion F j p ≫
    (JTJointRelativeGraphFamily.coefficient (L := L)).map (𝟙 p.1) at hh
  exact hh.trans ((congrArg (fun u ↦ vertexInclusion F j p ≫ u)
    ((JTJointRelativeGraphFamily.coefficient (L := L)).map_id p.1)).trans
      (Category.comp_id _))

/-- The genuine coefficient subcomplex of the actual timed vertex support. -/
def vertexFace (p : Index F j) :
    (std.obj ((JTExactlyMarkedSourceDiagram.degrees F j).obj p)).Subcomplex :=
  SSet.Subcomplex.range (std.map (vertexInclusion F j p))

/-- The genuine coefficient subcomplex of one whole timed bead. -/
def beadFace (p : Index F j) (B : (gap F j p).Bead) :
    (std.obj ((JTExactlyMarkedSourceDiagram.degrees F j).obj p)).Subcomplex :=
  SSet.Subcomplex.range (std.map (beadInclusion F j p B))

/-- Every incident bead face contains the entire actual vertex face. -/
theorem vertexFace_le_beadFace (p : Index F j) (B : (gap F j p).Bead)
    (h : Incident F j p B) : vertexFace F j p ≤ beadFace F j p B := by
  rw [vertexFace, beadFace, ← vertexToBead_inclusion F j p B h, std.map_comp]
  exact Subfunctor.range_comp_le _ _

private theorem support_range {d k : SimplexCategory}
    (s : std.obj d ⟶ J.obj k) :
    SSet.Subcomplex.range (std.map (JTRowGraphParameterSupport.inclusion s)) =
      SSet.stdSimplex.face (JTRowGraphParameterSupport.used s) := by
  induction k using SimplexCategory.rec with
  | _ n =>
    rw [SSet.Subcomplex.range_eq_ofSimplex]
    exact (SSet.stdSimplex.face_eq_ofSimplex _ _
      (JTRowGraphParameterSupport.supportOrderIso s)).symm

/-- The actual finite coefficient vertices used by the entire selected vertex prism. -/
def vertexSet (p : Index F j) :=
  JTRowGraphParameterSupport.used (JTPrismRectangle.sample ⦋0⦌ (time.obj p.1) ≫
    fullBeadParameter F p.1 0 (vertexNative F j p))

/-- The actual finite coefficient vertices used by the entire incident bead prism. -/
def beadSet (p : Index F j) (B : (gap F j p).Bead) :=
  JTRowGraphParameterSupport.used (JTPrismRectangle.sample ⦋B.length⦌ (time.obj p.1) ≫
    fullBeadParameter F p.1 B.length (beadNative F j p B))

/-- The vertex subcomplex is precisely the face on its actual used vertices. -/
theorem vertexFace_eq_face (p : Index F j) :
    vertexFace F j p = SSet.stdSimplex.face (vertexSet F j p) := support_range _

/-- The bead subcomplex is precisely the face on its actual used vertices. -/
theorem beadFace_eq_face (p : Index F j) (B : (gap F j p).Bead) :
    beadFace F j p B = SSet.stdSimplex.face (beadSet F j p B) := support_range _

/-- The full actual vertex prism always uses at least one coefficient vertex. -/
theorem vertexSet_nonempty (p : Index F j) : (vertexSet F j p).Nonempty :=
  JTRowGraphParameterSupport.used_nonempty _

/-- The actual vertex set is contained in every incident bead's actual vertex set. -/
theorem vertexSet_subset_beadSet (p : Index F j) (B : (gap F j p).Bead)
    (h : Incident F j p B) : vertexSet F j p ⊆ beadSet F j p B := by
  apply (SSet.stdSimplex.face_le_face_iff _ _).mp
  rw [← vertexFace_eq_face, ← beadFace_eq_face]
  exact vertexFace_le_beadFace F j p B h

/-- Union of faces, without inserting the simplex spanned by their union of vertices. -/
def support (p : Index F j) :
    (std.obj ((JTExactlyMarkedSourceDiagram.degrees F j).obj p)).Subcomplex :=
  vertexFace F j p ⊔ ⨆ B : {B : (gap F j p).Bead // Incident F j p B}, beadFace F j p B.val

/-- The vertex face remains present even when the inverse interval has no positive bead. -/
theorem vertexFace_le_support (p : Index F j) : vertexFace F j p ≤ support F j p :=
  le_sup_left

/-- Each actual incident bead face includes in the union. -/
theorem beadFace_le_support (p : Index F j) (B : (gap F j p).Bead)
    (h : Incident F j p B) : beadFace F j p B ≤ support F j p :=
  le_sup_of_le_right (le_iSup (fun B : {B : (gap F j p).Bead // Incident F j p B} ↦
    beadFace F j p B.val) ⟨B, h⟩)

/-- The actual old vertex row is the same horizontal face of the full original bead coefficient. -/
theorem row_face (p : Index F j) (B : (gap F j p).Bead)
    (h : Incident F j p B) :
    JTActualSourceJointSupport.oldVertexRow (L := L) p.1 p.2.val =
      JTParametrizedBeadGraph.coefficient (a := p.1) B.length (beadNative F j p B) ≫
        JTMixedGraphEndpointLifts.rowVertex W ⦋B.length⦌ (beadCoordinate F j p B h) := by
  rw [JTActualSourceJointSupport.oldVertexRow_eq_bead F p.1 j
    p.2.val p.2.property]
  apply JTParametrizedBeadGraph.coefficient_horizontal
  have hh := vertex_horizontal F j p B h
  rw [(codes L).map_id] at hh
  change (singleIso 0).inv ≫ vertexNative F j p ≫ 𝟙 _ = _ at hh
  rw [Category.comp_id] at hh
  exact hh

/-- The same actual row is stationary on the WHOLE bead support, not only its vertex support. -/
theorem row_on_beadSupport (p : Index F j) (B : (gap F j p).Bead)
    (h : Incident F j p B) :
    std.map (beadInclusion F j p B) ≫
        JTActualSourceJointSupport.oldVertexRow (L := L) p.1 p.2.val =
      term (std.obj (beadSupport F j p B)) ≫
        vertexPoint W (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j) := by
  let z := JTParametrizedBeadGraph.jointCoefficient (Q := Q) j
  let c := SSet.yonedaEquiv.symm
    (JTParametrizedBeadGraph.beadLabel (a := p.1) B.length (beadNative F j p B))
  have hc : std.map (beadInclusion F j p B) ≫ c =
      JTConstantOrderedLabel.constantCoefficient W z (single B.length)
        (beadSupport F j p B) := by
    exact coefficient_supported F j p.1 B.length (beadIntoGap F j p B)
      (beadNative F j p B) rfl
  have hr : JTParametrizedBeadGraph.coefficient (a := p.1)
        B.length (beadNative F j p B) ≫ JTNativeRowLabel.labelFromRow W B.length = c := by
    apply SSet.yonedaEquiv.injective
    simpa only [c, Equiv.apply_symm_apply] using
      JTParametrizedBeadGraph.coefficient_label (a := p.1)
        B.length (beadNative F j p B)
  haveI : Mono (TwoBeadEndpointLabel.jointLabelFromRow W) := by
    change Mono (OrderedSimplexEndpointFiber.freeSimplexRowIso W 0).inv
    infer_instance
  apply (cancel_mono (TwoBeadEndpointLabel.jointLabelFromRow W)).mp
  calc
    _ = (std.map (beadInclusion F j p B) ≫ c) ≫
        pre W (pointAt (single B.length) (ULift.up (beadCoordinate F j p B h))) := by
      rw [row_face F j p B h]
      have h := congrArg (fun q ↦ std.map (beadInclusion F j p B) ≫ q ≫
        pre W (pointAt (single B.length) (ULift.up (beadCoordinate F j p B h)))) hr
      simpa only [Category.assoc, JTNativeRowLabel.labelFromRow_vertex] using h
    _ = JTConstantOrderedLabel.constantCoefficient W z (single B.length)
        (beadSupport F j p B) ≫
          pre W (pointAt (single B.length) (ULift.up (beadCoordinate F j p B h))) := by
      rw [hc]
    _ = term (std.obj (beadSupport F j p B)) ≫
        OrderedNecklaceVertexPoints.zeroPoint W z := constant_at_point _ _ _ _ _
    _ = _ := by rw [Category.assoc, TwoBeadEndpointLabel.jointLabelFromRow_vertex]

private theorem range_agrees {X Y Z : SSet.{0}} (f : X ⟶ Y) (r c : Y ⟶ Z)
    (h : f ≫ r = f ≫ c) : (SSet.Subcomplex.range f).ι ≫ r =
      (SSet.Subcomplex.range f).ι ≫ c := by
  ext n x
  obtain ⟨y, hy⟩ := x.property
  have hh := congrFun (NatTrans.congr_app h n) y
  change r.app n x.val = c.app n x.val
  change r.app n (f.app n y) = c.app n (f.app n y) at hh
  rw [hy] at hh
  exact hh

private theorem union_agrees {X Y : SSet.{0}} (r c : X ⟶ Y)
    (U V : X.Subcomplex) (hU : U.ι ≫ r = U.ι ≫ c)
    (hV : V.ι ≫ r = V.ι ≫ c) :
    (U ⊔ V).ι ≫ r = (U ⊔ V).ι ≫ c := by
  ext n x
  rcases x.property with hx | hx
  · exact congrFun (NatTrans.congr_app hU n) ⟨x.val, hx⟩
  · exact congrFun (NatTrans.congr_app hV n) ⟨x.val, hx⟩

private theorem iSup_agrees {X Y : SSet.{0}} (r c : X ⟶ Y) {ι : Type}
    (U : ι → X.Subcomplex) (h : ∀ i, (U i).ι ≫ r = (U i).ι ≫ c) :
    (⨆ i, U i).ι ≫ r = (⨆ i, U i).ι ≫ c := by
  ext n x
  have hx := x.property
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion] at hx
  obtain ⟨i, hi⟩ := hx
  exact congrFun (NatTrans.congr_app (h i) n) ⟨x.val, hi⟩

private theorem constant_comp {X Y : SSet.{0}} (f : X ⟶ Y) {Z : SSet.{0}}
    (z : (Δ[0] : SSet.{0}) ⟶ Z) :
    f ≫ (term Y ≫ z) = term X ≫ z := by
  rw [← Category.assoc]
  congr 1

/-- The old vertex row is stationary on each entire genuine incident bead face. -/
theorem row_on_beadFace (p : Index F j) (B : (gap F j p).Bead)
    (h : Incident F j p B) :
    (beadFace F j p B).ι ≫ (JTExactlyMarkedSourceDiagram.endpointRows F j).app p =
      term (beadFace F j p B).toSSet ≫
        vertexPoint W (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j) := by
  rw [← constant_comp]
  apply range_agrees
  rw [constant_comp]
  exact row_on_beadSupport F j p B h

/-- The original vertex row is stationary on the full union of incident timed faces. -/
theorem row_on_support (p : Index F j) :
    (support F j p).ι ≫ (JTExactlyMarkedSourceDiagram.endpointRows F j).app p =
      term (support F j p).toSSet ≫
        vertexPoint W (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j) := by
  rw [← constant_comp]
  apply union_agrees
  · apply range_agrees
    rw [constant_comp]
    exact JTExactlyMarkedSourceDiagram.supported_endpoint F j p
  · apply iSup_agrees
    intro B
    rw [constant_comp]
    exact row_on_beadFace F j p B.val B.property

/-- The full original-time parameter supported at the actual vertex. -/
abbrev vertexParameter (p : Index F j) :=
  JTJointTimedEndpointSupport.supportedTimedParameter F p.1 j (liftedVertex F j p)

/-- The full original-time parameter supported on the whole incident bead. -/
abbrev beadParameter (p : Index F j) (B : (gap F j p).Bead) :=
  JTPrismRectangle.supportedParameter (fullBeadParameter F p.1 B.length (beadNative F j p B))

/-- The exact vertex restriction commutes with the entire independent original time. -/
theorem parameter_square (p : Index F j) (B : (gap F j p).Bead)
    (h : Incident F j p B) :
    (std.map (vertexOperator F j p B h) ⊗ₘ 𝟙 (J.obj (time.obj p.1))) ≫
        beadParameter F j p B =
      vertexParameter F j p ≫ J.map (vertexToBead F j p B h) := by
  have hh := JTParametrizedBeadGraph.supportedFullBeadParameter_map F (𝟙 p.1)
    (i := vertexNative F j p) (i' := beadNative F j p B)
    (vertexOperator F j p B h) (vertex_horizontal F j p B h)
  change (std.map (vertexOperator F j p B h) ⊗ₘ J.map (time.map (𝟙 p.1))) ≫
    beadParameter F j p B = vertexParameter F j p ≫ J.map (vertexToBead F j p B h) at hh
  rw [time.map_id, J.map_id] at hh
  exact hh

/-- Both supported descriptions factor through the unchanged original coefficient/time map. -/
theorem parameter_original (p : Index F j) (B : (gap F j p).Bead)
    (h : Incident F j p B) :
    (vertexParameter F j p ≫ J.map (vertexToBead F j p B h)) ≫
        J.map (beadInclusion F j p B) =
      JTActualSourceJointSupport.timeParameter F p.1 p.2.val := by
  rw [Category.assoc, ← J.map_comp, vertexToBead_inclusion]
  exact JTActualSourceJointSupport.timeParameter_factor F p.1 j p.2.val p.2.property

end
end DaggerModels.PartII.JTIncidentBeadSupportData
