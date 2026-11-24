import DaggerModelsPartII.JTJointSubdivisionPieces
import DaggerModelsPartII.JTIncidentChartSupport

/-!
# The actual inserted vertex in its given coarse chart

The interval inclusion contains every original vertex between its endpoints.
Transport through the actual chart isomorphism gives the inserted vertex a
unique chart coordinate, including both endpoints and zero-length charts.
Naturality is derived from uniqueness and the original insertion operators;
no natural choice of enclosing brackets is assumed.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTInsertionMiddleChartVertex

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row)
open JTTargetJointMarks (Joint)

noncomputable section

private abbrev std := SSet.stdSimplex.{0}

private theorem interval_orderMap (T : NecklaceCode) (a c : Fin (T.len + 1)) (hac : a ≤ c)
    (w : Fin ((intervalCode T a c hac).len + 1)) :
    orderMap (intervalι T a c hac) w = intervalEmbedding T a c hac w :=
  congrArg ULift.down (intervalι_vertices T a c hac (ULift.up w))

private theorem interval_iso_preimage (T : NecklaceCode)
    (a c b : Fin (T.len + 1)) (hac : a ≤ c) (hab : a ≤ b) (hbc : b ≤ c)
    {d : ℕ} (e : intervalCode T a c hac ≅ single d) :
    ∃ ν : Fin (d + 1), orderMap (e.inv.map ≫ intervalι.{0} T a c hac) ν = b := by
  obtain ⟨w, hw⟩ := intervalEmbedding_preimage T a c hac b hab hbc
  refine ⟨orderMap e.hom.map w, ?_⟩
  have hi : e.hom.map ≫ e.inv.map = 𝟙 (intervalCode T a c hac).toSSet :=
    congrArg (fun f : intervalCode T a c hac ⟶ intervalCode T a c hac ↦ f.map)
      e.hom_inv_id
  rw [orderMap_comp_apply, ← orderMap_comp_apply e.hom.map e.inv.map, hi]
  have hid : orderMap (𝟙 ((intervalCode T a c hac).toSSet : SSet.{0})) w = w := by
    change (mapVertices (𝟙 ((intervalCode T a c hac).toSSet : SSet.{0})) (ULift.up w)).down = w
    rw [mapVertices_id]
    rfl
  rw [hid, interval_orderMap]
  exact hw

private theorem interval_iso_mono (T : NecklaceCode)
    (a c : Fin (T.len + 1)) (hac : a ≤ c) {d : ℕ}
    (e : intervalCode T a c hac ≅ single d) :
    Mono (e.inv.map ≫ intervalι.{0} T a c hac) := by
  haveI : IsIso e.inv.map := by
    change IsIso (NecklaceCode.simplicialFunctor.map e.inv)
    infer_instance
  infer_instance

private theorem orderMap_injective {T U : NecklaceCode} (f : (T.toSSet : SSet.{0}) ⟶ U.toSSet)
    [Mono f] : Function.Injective (orderMap f) := by
  intro a b h
  have hp : pointAt T (ULift.up a) ≫ f = pointAt T (ULift.up b) ≫ f := by
    rw [pointAt_comp, pointAt_comp]
    congr 1
    apply ULift.ext
    exact h
  have he := congrArg (fun p : (Δ[0] : SSet.{0}) ⟶ T.toSSet ↦
    (T.verticesEquiv (SSet.yonedaEquiv p)).down) ((cancel_mono f).mp hp)
  simpa only [pointAt_vertex, Equiv.apply_symm_apply] using he

private theorem elements_functor_ext {C B : Type} [SmallCategory C] [SmallCategory B]
    {V : C ⥤ Type} {G H : B ⥤ V.Elements}
    (hobj : ∀ p, G.obj p = H.obj p)
    (hbase : G ⋙ CategoryOfElements.π V = H ⋙ CategoryOfElements.π V) : G = H := by
  refine CategoryTheory.Functor.ext hobj ?_
  intro p q f
  let π := CategoryOfElements.π V
  apply CategoryOfElements.ext V
  change π.map (G.map f) = π.map (eqToHom (hobj p) ≫ H.map f ≫ eqToHom (hobj q).symm)
  rw [π.map_comp, π.map_comp, eqToHom_map, eqToHom_map]
  exact Functor.congr_hom hbase f

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code)

/-- The actual insertion source, which already retains its given enclosing chart. -/
abbrev Index := JTJointSubdivisionInsertion.Index F j

private abbrev charts := JTJointSubdivisionInsertion.toCharts F j
private abbrev base := JTJointSubdivisionInsertion.base F j
private abbrev D := JTJointSubdivisionBeadNormalization.degrees F j
private abbrev native := JTJointSubdivisionBeadNormalization.inclusion F j
private abbrev T (p : Index F j) := (codes L).obj ((base F j).obj p)

private theorem native_eq (p : Index F j) : native F j p.1 =
    (JTJointSubdivisionBeadCharts.simplexIso F j p.1).inv.map ≫
      intervalι (T F j p) p.1.2.firstCut p.1.2.lastCut p.1.2.adjacent.2.2.1 := rfl

/-- Every actual inserted cut has a coordinate in its GIVEN coarse chart. -/
theorem coordinate_exists (p : Index F j) :
    ∃ ν : Fin (((D F j).obj p.1).len + 1),
      JTJointSubdivisionVertexSupport.cut F j p.1 ν = p.2.val := by
  have h := interval_iso_preimage (T F j p) p.1.2.firstCut p.1.2.lastCut p.2.val
    p.1.2.adjacent.2.2.1 p.2.property.1 p.2.property.2
    (JTJointSubdivisionBeadCharts.simplexIso F j p.1)
  change ∃ ν : Fin (((D F j).obj p.1).len + 1), orderMap (native F j p.1) ν = p.2.val
  rw [native_eq]
  exact h

/-- The selected coordinate belongs to the actual chart; it does not select enclosing brackets. -/
def coordinate (p : Index F j) : Fin (((D F j).obj p.1).len + 1) :=
  Classical.choose (coordinate_exists F j p)

/-- Its actual original source cut is EXACTLY the inserted cut. -/
theorem cut_coordinate (p : Index F j) :
    JTJointSubdivisionVertexSupport.cut F j p.1 (coordinate F j p) = p.2.val :=
  Classical.choose_spec (coordinate_exists F j p)

private theorem cut_injective (p : Index F j) :
    Function.Injective (JTJointSubdivisionVertexSupport.cut F j p.1) := by
  haveI : Mono (native F j p.1) := by
    rw [native_eq]
    exact interval_iso_mono (T F j p) p.1.2.firstCut p.1.2.lastCut p.1.2.adjacent.2.2.1
      (JTJointSubdivisionBeadCharts.simplexIso F j p.1)
  exact orderMap_injective (native F j p.1)

/-- The actual chart coordinate is unique, including coalesced and zero-length charts. -/
theorem coordinate_unique (p : Index F j) (ν : Fin (((D F j).obj p.1).len + 1))
    (hν : JTJointSubdivisionVertexSupport.cut F j p.1 ν = p.2.val) :
    ν = coordinate F j p :=
  cut_injective F j p (hν.trans (cut_coordinate F j p).symm)

private theorem cut_map {p q : JTJointSubdivisionBeadCharts.Index F j} (f : p ⟶ q)
    (ν : Fin (((D F j).obj p).len + 1)) :
    JTJointSubdivisionVertexSupport.cut F j q (((D F j).map f).toOrderHom ν) =
      orderMap ((codes L).map ((JTJointSubdivisionBeadCharts.base F j).map f)).map
        (JTJointSubdivisionVertexSupport.cut F j p ν) := by
  have h := congrArg (fun u : (single ((D F j).obj p).len).toSSet ⟶
      ((codes L).obj ((JTJointSubdivisionBeadCharts.base F j).obj q)).toSSet ↦
        orderMap u ν) (JTJointSubdivisionBeadNormalization.inclusion_natural F j f)
  simpa only [orderMap_comp_apply] using h

/-- Naturality follows from uniqueness and actual insertion transport, with no chosen section. -/
theorem coordinate_natural {p q : Index F j} (f : p ⟶ q) :
    ((D F j).map f.val).toOrderHom (coordinate F j p) = coordinate F j q := by
  apply cut_injective F j q
  rw [cut_map, cut_coordinate, cut_coordinate]
  exact congrArg Subtype.val f.property

/-- The actual inserted point in its given chart varies under every original insertion arrow. -/
def toVertex : Index F j ⥤ JTJointSubdivisionVertexSupport.VertexIndex F j where
  obj p := ⟨p.1, coordinate F j p⟩
  map f := ⟨f.val, coordinate_natural F j f⟩
  map_id p := by apply CategoryOfElements.ext; rfl
  map_comp f g := by apply CategoryOfElements.ext; rfl

/-- This construction retains the given enclosing chart and every original chart operator. -/
theorem toVertex_toCharts :
    toVertex F j ⋙ JTJointSubdivisionVertexSupport.toCharts F j = charts F j := rfl

/-- The chart vertex is the actual inserted mark, including its exact original source object. -/
theorem toVertex_marked_obj (p : Index F j) :
    (JTJointSubdivisionVertexSupport.toMarked F j).obj ((toVertex F j).obj p) =
      (JTJointSubdivisionInsertion.insertedCut F j).obj p := by
  refine Functor.Elements.ext (F := JTExactlyMarkedSourceDiagram.vertices F j)
    ((JTJointSubdivisionVertexSupport.toMarked F j).obj ((toVertex F j).obj p))
    ((JTJointSubdivisionInsertion.insertedCut F j).obj p) rfl ?_
  simp only [eqToHom_refl, FunctorToTypes.map_id_apply]
  exact Subtype.ext (cut_coordinate F j p)

/-- The full marked functor agrees with the actual inserted-cut functor on every arrow. -/
theorem toVertex_toMarked :
    toVertex F j ⋙ JTJointSubdivisionVertexSupport.toMarked F j =
      JTJointSubdivisionInsertion.insertedCut F j :=
  elements_functor_ext (toVertex_marked_obj F j) rfl

private theorem support_eq_of_cut (a : A)
    (v w : (JTExactlyMarkedSourceDiagram.vertices F j).obj a) (h : v = w) :
    JTIncidentBeadSupportData.support F j ⟨a, v⟩ =
      JTIncidentBeadSupportData.support F j ⟨a, w⟩ := by
  subst w
  rfl

/-- The ENTIRE coarse chart timed face lies in the incident union at the inserted cut. -/
theorem coarse_face_le_support (p : Index F j) :
    SSet.Subcomplex.range (std.map (JTJointSubdivisionVertexSupport.beadInclusion F j p.1)) ≤
      JTIncidentBeadSupportData.support F j
        ((JTJointSubdivisionInsertion.insertedCut F j).obj p) := by
  have he : ((JTJointSubdivisionVertexSupport.toMarked F j).obj
      ((toVertex F j).obj p)).2 =
        ((JTJointSubdivisionInsertion.insertedCut F j).obj p).2 :=
    Subtype.ext (cut_coordinate F j p)
  have hs := support_eq_of_cut F j ((base F j).obj p)
    (((JTJointSubdivisionVertexSupport.toMarked F j).obj ((toVertex F j).obj p)).2)
    (((JTJointSubdivisionInsertion.insertedCut F j).obj p).2) he
  change SSet.Subcomplex.range
    (std.map (JTJointSubdivisionVertexSupport.beadInclusion F j p.1)) ≤
      JTIncidentBeadSupportData.support F j
        ⟨(base F j).obj p, ((JTJointSubdivisionInsertion.insertedCut F j).obj p).2⟩
  rw [← hs]
  exact JTIncidentChartSupport.face_le_support F j ((toVertex F j).obj p)

end
end DaggerModels.PartII.JTInsertionMiddleChartVertex
