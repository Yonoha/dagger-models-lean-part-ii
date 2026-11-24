import DaggerModelsPartII.JTIncidentBeadSupportData
import DaggerModelsPartII.JTIncidentBeadImages
import DaggerModelsPartII.JTActualJointGapVertexTransport

/-!
The genuine incident-support union is covariant under every original exact-cut
operator. Each whole-bead generator maps into an actual incident bead or vertex
generator. The induced support map is the restriction of the ORIGINAL coefficient
operator, independent of the existential bead factor. No functorial choice of a
maximal bead, flanked flag, or endpoint-preserving bead operator is assumed.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTIncidentBeadSupportTransport

open JTParametrizedTargetFamilies (Family codes)
open JTTargetJointMarks (Joint)
open JTProjectiveOrderedFiberComparison (row)
open JTIncidentBeadSupportData

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev J := GroupoidSimplex.parameter

private theorem image_range_of_fac {X Y X' Y' : SSet.{0}}
    (s : X ⟶ Y) (t : X' ⟶ Y') (g : Y ⟶ Y') (h : X ⟶ X')
    (fac : s ≫ g = h ≫ t) :
    (SSet.Subcomplex.range s).image g ≤ SSet.Subcomplex.range t := by
  rw [← SSet.Subcomplex.range_comp, fac]
  exact Subfunctor.range_comp_le _ _

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time) (j : Joint Q.code)

private abbrev K := JTExactlyMarkedSourceDiagram.degrees F j
private abbrev gapMap {p q : Index F j} (f : p ⟶ q) :=
  (JTActualJointGapVertexTransport.overlap F j).map f

/-- The existing actual vertex-used face transports by the unchanged coefficient operator. -/
theorem vertexFace_image {p q : Index F j} (f : p ⟶ q) :
    (vertexFace F j p).image (std.map ((K F j).map f)) ≤ vertexFace F j q := by
  apply image_range_of_fac (std.map (vertexInclusion F j p))
    (std.map (vertexInclusion F j q)) (std.map ((K F j).map f))
    (std.map ((JTExactlyMarkedSourceDiagram.supports F j).map f))
  simpa only [std.map_comp] using
    (congrArg std.map ((JTExactlyMarkedSourceDiagram.incl F j).naturality f)).symm

private theorem bead_native_factor {p q : Index F j} (f : p ⟶ q)
    (B : (gap F j p).Bead) (C : (gap F j q).Bead)
    (u : ⦋B.length⦌ ⟶ ⦋C.length⦌)
    (h : std.map u ≫ (gap F j q).beadSimplex C =
      (gap F j p).beadSimplex B ≫ gapMap F j f) :
    (singleIso B.length).inv ≫ beadNative F j p B ≫ ((codes L).map f.val).map =
      std.map u ≫ (singleIso C.length).inv ≫ beadNative F j q C := by
  have hh := congrArg (fun t : (Δ[B.length] : SSet.{0}) ⟶ (gap F j q).toSSet ↦
    t ≫ gapInclusion F j q) h
  simp only [Category.assoc, JTActualJointGapVertexTransport.map_fac] at hh
  simpa only [beadNative, beadIntoGap, Category.assoc, Iso.inv_hom_id_assoc] using hh.symm

private theorem beadFace_image_of_factor {p q : Index F j} (f : p ⟶ q)
    (B : (gap F j p).Bead) (C : (gap F j q).Bead)
    (u : ⦋B.length⦌ ⟶ ⦋C.length⦌)
    (h : std.map u ≫ (gap F j q).beadSimplex C =
      (gap F j p).beadSimplex B ≫ gapMap F j f) :
    (beadFace F j p B).image (std.map ((K F j).map f)) ≤ beadFace F j q C := by
  let σ := JTParametrizedBeadGraph.fullBeadSupportMap F f.val
    (i := beadNative F j p B) (i' := beadNative F j q C) u
    (bead_native_factor F j f B C u h)
  have hs : σ ≫ beadInclusion F j q C = beadInclusion F j p B ≫ (K F j).map f :=
    JTPrismRectangle.supportMap_inclusion _ _ _ _
      (JTParametrizedBeadGraph.fullBeadParameter_map F f.val
        (i := beadNative F j p B) (i' := beadNative F j q C) u
        (bead_native_factor F j f B C u h))
  apply image_range_of_fac (std.map (beadInclusion F j p B))
    (std.map (beadInclusion F j q C)) (std.map ((K F j).map f)) (std.map σ)
  simpa only [std.map_comp] using (congrArg std.map hs).symm

private abbrev vertexNative (p : Index F j) :=
  JTJointTimedEndpointSupport.vertexBead F p.1 j (liftedVertex F j p) ≫
    gapInclusion F j p

private theorem point_gap (p : Index F j) :
    pointAt (gap F j p) (ULift.up (gapCoordinate F j p)) =
      SSet.yonedaEquiv.symm (liftedVertex F j p) := by
  unfold pointAt gapCoordinate
  rw [Equiv.symm_apply_apply]

private theorem point_native_factor {p q : Index F j} (f : p ⟶ q)
    (B : (gap F j p).Bead) (u : ⦋B.length⦌ ⟶ ⦋0⦌)
    (h : std.map u ≫ pointAt (gap F j q) (ULift.up (gapCoordinate F j q)) =
      (gap F j p).beadSimplex B ≫ gapMap F j f) :
    (singleIso B.length).inv ≫ beadNative F j p B ≫ ((codes L).map f.val).map =
      std.map u ≫ (singleIso 0).inv ≫ vertexNative F j q := by
  have hh := congrArg (fun t : (Δ[B.length] : SSet.{0}) ⟶ (gap F j q).toSSet ↦
    t ≫ gapInclusion F j q) h
  simp only [Category.assoc, JTActualJointGapVertexTransport.map_fac, point_gap] at hh
  simpa only [beadNative, beadIntoGap, vertexNative,
    JTJointTimedEndpointSupport.vertexBead, Category.assoc,
    Iso.inv_hom_id_assoc] using hh.symm

private theorem beadFace_image_to_vertex {p q : Index F j} (f : p ⟶ q)
    (B : (gap F j p).Bead) (u : ⦋B.length⦌ ⟶ ⦋0⦌)
    (h : std.map u ≫ pointAt (gap F j q) (ULift.up (gapCoordinate F j q)) =
      (gap F j p).beadSimplex B ≫ gapMap F j f) :
    (beadFace F j p B).image (std.map ((K F j).map f)) ≤ vertexFace F j q := by
  let σ := JTParametrizedBeadGraph.fullBeadSupportMap F f.val
    (i := beadNative F j p B) (i' := vertexNative F j q) u
    (point_native_factor F j f B u h)
  have hs : σ ≫ vertexInclusion F j q = beadInclusion F j p B ≫ (K F j).map f :=
    JTPrismRectangle.supportMap_inclusion _ _ _ _
      (JTParametrizedBeadGraph.fullBeadParameter_map F f.val
        (i := beadNative F j p B) (i' := vertexNative F j q) u
        (point_native_factor F j f B u h))
  apply image_range_of_fac (std.map (beadInclusion F j p B))
    (std.map (vertexInclusion F j q)) (std.map ((K F j).map f)) (std.map σ)
  simpa only [std.map_comp] using (congrArg std.map hs).symm

/-- Every actual incident bead used face maps into the SAME target incident union. -/
theorem beadFace_image {p q : Index F j} (f : p ⟶ q)
    (B : (gap F j p).Bead) (hB : Incident F j p B) :
    (beadFace F j p B).image (std.map ((K F j).map f)) ≤ support F j q := by
  have hv : orderMap (gapMap F j f) (gapCoordinate F j p) = gapCoordinate F j q :=
    JTActualJointGapVertexTransport.coordinate_map F j f
  rcases JTIncidentBeadImages.incident_image (gapMap F j f) B
      (gapCoordinate F j p) hB with ⟨C, u, hC, h⟩ | ⟨u, h⟩
  · rw [hv] at hC
    exact (beadFace_image_of_factor F j f B C u h).trans
      (beadFace_le_support F j q C hC)
  · rw [hv] at h
    exact (beadFace_image_to_vertex F j f B u h).trans (vertexFace_le_support F j q)

/-- Canonical image containment, without choosing a functorial maximal-bead witness. -/
theorem support_image {p q : Index F j} (f : p ⟶ q) :
    (support F j p).image (std.map ((K F j).map f)) ≤ support F j q := by
  apply (SSet.Subcomplex.image_le_iff _ _ _).mpr
  apply sup_le
  · exact (SSet.Subcomplex.image_le_iff _ _ _).mp
      ((vertexFace_image F j f).trans (vertexFace_le_support F j q))
  · apply iSup_le
    intro B
    exact (SSet.Subcomplex.image_le_iff _ _ _).mp (beadFace_image F j f B.val B.property)

/-- Restrict the original coefficient operator to the genuine support union. -/
def supportMap {p q : Index F j} (f : p ⟶ q) :
    (support F j p).toSSet ⟶ (support F j q).toSSet :=
  (support F j q).lift ((support F j p).ι ≫ std.map ((K F j).map f)) (by
    rw [← SSet.Subcomplex.image_eq_range]
    exact support_image F j f)

/-- The restricted map retains the literal original coefficient square. -/
theorem supportMap_fac {p q : Index F j} (f : p ⟶ q) :
    supportMap F j f ≫ (support F j q).ι =
      (support F j p).ι ≫ std.map ((K F j).map f) := rfl

/-- The actual incident support union is a strict functor on every original exact-cut arrow. -/
def diagram : Index F j ⥤ SSet.{0} where
  obj p := (support F j p).toSSet
  map := supportMap F j
  map_id p := by
    apply (cancel_mono (support F j p).ι).mp
    rw [supportMap_fac, (K F j).map_id, std.map_id, Category.comp_id, Category.id_comp]
  map_comp {p q r} f g := by
    apply (cancel_mono (support F j r).ι).mp
    simp only [Category.assoc, supportMap_fac, (K F j).map_comp, std.map_comp]
    rw [← Category.assoc (supportMap F j f), supportMap_fac, Category.assoc]

/-- The natural full support inclusion in the original coefficient simplex. -/
def inclusion : diagram F j ⟶ (K F j) ⋙ std where
  app p := (support F j p).ι
  naturality _ _ f := supportMap_fac F j f

/-- The entire original vertex support includes naturally in the incident union. -/
def vertexToSupport : JTExactlyMarkedSourceDiagram.supports F j ⋙ std ⟶ diagram F j where
  app p := (support F j p).lift (std.map (vertexInclusion F j p))
    (vertexFace_le_support F j p)
  naturality {p q} f := by
    apply (cancel_mono (support F j q).ι).mp
    change std.map ((JTExactlyMarkedSourceDiagram.supports F j).map f) ≫
        (support F j q).lift (std.map (vertexInclusion F j q))
          (vertexFace_le_support F j q) ≫ (support F j q).ι =
      (support F j p).lift (std.map (vertexInclusion F j p))
          (vertexFace_le_support F j p) ≫
        supportMap F j f ≫ (support F j q).ι
    simp only [SSet.Subcomplex.lift_ι, supportMap_fac]
    rw [← Category.assoc, SSet.Subcomplex.lift_ι]
    simpa only [← std.map_comp] using
      congrArg std.map ((JTExactlyMarkedSourceDiagram.incl F j).naturality f)

/-- The natural incident inclusion retains the same old coefficient face exactly. -/
theorem vertexToSupport_fac : vertexToSupport F j ≫ inclusion F j =
    Functor.whiskerRight (JTExactlyMarkedSourceDiagram.incl F j) std := by
  apply NatTrans.ext
  funext p
  rfl

end
end DaggerModels.PartII.JTIncidentBeadSupportTransport
