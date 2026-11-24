import DaggerModelsPartII.JTJointPairSubdivisionDiagram
import DaggerModelsPartII.JTJointPairGapDiagram
import ChosenNecklaceIntervalSingle

/-!
Actual simplex charts between adjacent subdivision cuts. Adjacency excludes
every interior subdivision cut, hence every interior original native joint.
Exact original pair arrows transport these charts to their literal image
subdivision, including when their two endpoints coalesce. Refinements that
insert a cut inside a chart require a separate subdivision comparison.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTJointSubdivisionBeadCharts

open JTParametrizedTargetFamilies (Family codes)
open JTTargetJointMarks (Joint)
open JTProjectiveOrderedFiberComparison (row)
open JTJointPairSubdivisionDiagram (Subdivision transport)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time) (j : Joint Q.code)

private abbrev E := JTJointPairSourceDiagram.Index F j
private abbrev T (p : E F j) := (codes L).obj p.1
private abbrev vertices {p q : E F j} (f : p ⟶ q) :=
  orderMap ((codes L).map f.val).map

/-- Two cuts in the actual subdivision with no subdivision cut strictly between them.
The diagonal case is retained as a point chart. -/
def Adjacent (p : E F j) (C : Subdivision F j p)
    (a b : Fin ((T F j p).len + 1)) : Prop :=
  a ∈ C.val ∧ b ∈ C.val ∧ a ≤ b ∧
    (∀ t ∈ C.val, a < t → t < b → False)

/-- Adjacency in an admissible cut set excludes every interior original native joint. -/
theorem no_interior_joint (p : E F j) (C : Subdivision F j p)
    (a b : Fin ((T F j p).len + 1)) (h : Adjacent F j p C a b)
    (t : Fin ((T F j p).len + 1)) (ht : t ∈ (T F j p).joints)
    (ha : a < t) (hb : t < b) : False := by
  have hC : t ∈ C.val := C.property.2.2.2 t ht
    ((C.property.2.2.1 a h.1).1.trans ha.le)
    (hb.le.trans (C.property.2.2.1 b h.2.1).2)
  exact h.2.2.2 t hC ha hb

/-- The actual adjacent-cut interval is one simplex, including a zero-length interval. -/
theorem interval_eq_single (p : E F j) (C : Subdivision F j p)
    (a b : Fin ((T F j p).len + 1)) (h : Adjacent F j p C a b) :
    intervalCode (T F j p) a b h.2.2.1 = single (b.val - a.val) := by
  apply code_ext (T := intervalCode (T F j p) a b h.2.2.1)
    (U := single (b.val - a.val)) rfl
  apply heq_of_eq
  ext k
  constructor
  · intro hk
    rcases (intervalCode_joint (T F j p) a b h.2.2.1 k).mp hk with h0 | h1 | hj
    · exact (mem_single_joints _ k).mpr (Or.inl h0)
    · exact (mem_single_joints _ k).mpr (Or.inr h1)
    · let t := intervalEmbedding (T F j p) a b h.2.2.1 k
      have ht := intervalEmbedding_bounds (T F j p) a b h.2.2.1 k
      by_cases hta : t = a
      · apply (mem_single_joints _ k).mpr
        left
        apply (intervalEmbedding (T F j p) a b h.2.2.1).injective
        exact hta.trans (intervalEmbedding_first (T F j p) a b h.2.2.1).symm
      · by_cases htb : t = b
        · apply (mem_single_joints _ k).mpr
          right
          apply (intervalEmbedding (T F j p) a b h.2.2.1).injective
          exact htb.trans (intervalEmbedding_last (T F j p) a b h.2.2.1).symm
        · exact False.elim (no_interior_joint F j p C a b h t hj
            (lt_of_le_of_ne ht.1 (Ne.symm hta)) (lt_of_le_of_ne ht.2 htb))
  · intro hk
    rcases (mem_single_joints _ k).mp hk with h0 | h1
    · exact (intervalCode_joint (T F j p) a b h.2.2.1 k).mpr (Or.inl h0)
    · exact (intervalCode_joint (T F j p) a b h.2.2.1 k).mpr (Or.inr (Or.inl h1))

/-- The canonical actual code isomorphism preserves the original ordered interval endpoints. -/
def chartIso (p : E F j) (C : Subdivision F j p)
    (a b : Fin ((T F j p).len + 1)) (h : Adjacent F j p C a b) :
    intervalCode (T F j p) a b h.2.2.1 ≅ single (b.val - a.val) :=
  eqToIso (interval_eq_single F j p C a b h)

/-- The first native endpoint is the actual first endpoint of the simplex chart. -/
theorem chartIso_first (p : E F j) (C : Subdivision F j p)
    (a b : Fin ((T F j p).len + 1)) (h : Adjacent F j p C a b) :
    (chartIso F j p C a b h).hom.map.app (op ⦋0⦌)
        (intervalCode (T F j p) a b h.2.2.1).first =
      (single (b.val - a.val)).first :=
  (chartIso F j p C a b h).hom.first

/-- The last native endpoint is retained by the same canonical chart. -/
theorem chartIso_last (p : E F j) (C : Subdivision F j p)
    (a b : Fin ((T F j p).len + 1)) (h : Adjacent F j p C a b) :
    (chartIso F j p C a b h).hom.map.app (op ⦋0⦌)
        (intervalCode (T F j p) a b h.2.2.1).last =
      (single (b.val - a.val)).last :=
  (chartIso F j p C a b h).hom.last

/-- Literal images of adjacent cuts remain adjacent in the image subdivision.
This does not assert adjacency in a further refinement of that subdivision. -/
theorem image_adjacent {p q : E F j} (f : p ⟶ q) (C : Subdivision F j p)
    (a b : Fin ((T F j p).len + 1)) (h : Adjacent F j p C a b) :
    Adjacent F j q (transport F j f C) (vertices F j f a) (vertices F j f b) := by
  refine ⟨Finset.mem_image.mpr ⟨a, h.1, rfl⟩,
    Finset.mem_image.mpr ⟨b, h.2.1, rfl⟩, (vertices F j f).monotone h.2.2.1, ?_⟩
  intro t ht ha hb
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
  have hau : a < u := by
    by_contra hn
    exact (not_le_of_gt ha) ((vertices F j f).monotone (le_of_not_gt hn))
  have hub : u < b := by
    by_contra hn
    exact (not_le_of_gt hb) ((vertices F j f).monotone (le_of_not_gt hn))
  exact h.2.2.2 u hu hau hub

/-- The exact native restriction on an adjacent interval and its possibly collapsed image. -/
def imageIntervalMap {p q : E F j} (f : p ⟶ q) (C : Subdivision F j p)
    (a b : Fin ((T F j p).len + 1)) (h : Adjacent F j p C a b) :
    intervalCode (T F j p) a b h.2.2.1 ⟶
      intervalCode (T F j q) (vertices F j f a) (vertices F j f b)
        ((vertices F j f).monotone h.2.2.1) :=
  DaggerOriginalProductGadget.intervalCodeHom ((codes L).map f.val).map
    a b h.2.2.1 (vertices F j f a) (vertices F j f b)
    ((vertices F j f).monotone h.2.2.1) rfl rfl

/-- The complete interval transport square commutes in the unchanged original source. -/
theorem imageIntervalMap_fac {p q : E F j} (f : p ⟶ q) (C : Subdivision F j p)
    (a b : Fin ((T F j p).len + 1)) (h : Adjacent F j p C a b) :
    (imageIntervalMap F j f C a b h).map ≫
        intervalι (T F j q) (vertices F j f a) (vertices F j f b)
          ((vertices F j f).monotone h.2.2.1) =
      intervalι (T F j p) a b h.2.2.1 ≫ ((codes L).map f.val).map :=
  DaggerOriginalProductGadget.necklaceIntervalMap_fac ((codes L).map f.val).map
    a b h.2.2.1 (vertices F j f a) (vertices F j f b)
    ((vertices F j f).monotone h.2.2.1) le_rfl le_rfl

/-- Exact image transport expressed on the two canonical single-simplex codes. -/
def imageSingleMap {p q : E F j} (f : p ⟶ q) (C : Subdivision F j p)
    (a b : Fin ((T F j p).len + 1)) (h : Adjacent F j p C a b) :
    single (b.val - a.val) ⟶
      single ((vertices F j f b).val - (vertices F j f a).val) :=
  (chartIso F j p C a b h).inv ≫ imageIntervalMap F j f C a b h ≫
    (chartIso F j q (transport F j f C) (vertices F j f a) (vertices F j f b)
      (image_adjacent F j f C a b h)).hom

/-- An actual adjacent interval remembers its ambient pair and its full subdivision. -/
@[ext]
structure Chart (p : E F j) where
  cuts : Subdivision F j p
  firstCut : Fin ((T F j p).len + 1)
  lastCut : Fin ((T F j p).len + 1)
  adjacent : Adjacent F j p cuts firstCut lastCut

private def chartTransport {p q : E F j} (f : p ⟶ q) (c : Chart F j p) : Chart F j q where
  cuts := transport F j f c.cuts
  firstCut := vertices F j f c.firstCut
  lastCut := vertices F j f c.lastCut
  adjacent := image_adjacent F j f c.cuts c.firstCut c.lastCut c.adjacent

private theorem vertex_id (p : E F j) (v : Fin ((T F j p).len + 1)) :
    vertices F j (𝟙 p) v = v := by
  change orderMap ((codes L).map (𝟙 p.1)).map v = v
  rw [(codes L).map_id]
  exact DaggerOriginalProductGadget.orderMap_id_apply _ _

private theorem vertex_comp {p q r : E F j} (f : p ⟶ q) (g : q ⟶ r)
    (v : Fin ((T F j p).len + 1)) :
    vertices F j (f ≫ g) v = vertices F j g (vertices F j f v) := by
  change orderMap ((codes L).map (f.val ≫ g.val)).map v = _
  rw [(codes L).map_comp]
  exact orderMap_comp_apply _ _ _

/-- Original pair arrows act on every actual adjacent chart by literal images. -/
def charts : E F j ⥤ Type where
  obj := Chart F j
  map := chartTransport F j
  map_id p := by
    funext c
    apply Chart.ext
    · exact JTJointPairSubdivisionDiagram.transport_id F j p c.cuts
    · exact vertex_id F j p c.firstCut
    · exact vertex_id F j p c.lastCut
  map_comp {p q r} f g := by
    funext c
    apply Chart.ext
    · exact JTJointPairSubdivisionDiagram.transport_comp F j f g c.cuts
    · exact vertex_comp F j f g c.firstCut
    · exact vertex_comp F j f g c.lastCut

/-- The actual image-chart source includes all original arrows and their coalescing images.
It does not identify cut-inserting refinement arrows with exact chart transport. -/
abbrev Index := (charts F j).Elements

private theorem cut_at_joint (p : E F j) (C : Subdivision F j p)
    (v : Fin ((T F j p).len + 1)) (hv : v ∈ C.val) :
    orderMap (F.collapse.app p.1).map v = j.val := by
  obtain ⟨hl, hr⟩ := C.property.2.2.1 v hv
  apply le_antisymm
  · exact ((orderMap (F.collapse.app p.1).map).monotone hr).trans p.2.right.property.le
  · exact p.2.left.property.symm.le.trans
      ((orderMap (F.collapse.app p.1).map).monotone hl)

private def intervalPair (p : Index F j) : E F j :=
  ⟨p.1.1,
    ⟨⟨p.2.firstCut, cut_at_joint F j p.1 p.2.cuts p.2.firstCut p.2.adjacent.1⟩,
      ⟨p.2.lastCut, cut_at_joint F j p.1 p.2.cuts p.2.lastCut p.2.adjacent.2.1⟩,
      p.2.adjacent.2.2.1⟩⟩

private theorem pair_ext {a : A} {p q : JTJointPairSourceDiagram.Pair F j a}
    (hl : p.left = q.left) (hr : p.right = q.right) : p = q := by
  cases p
  cases q
  cases hl
  cases hr
  rfl

/-- Regard the chart endpoints as their actual ordered pair above the SAME target joint. -/
def toPairs : Index F j ⥤ E F j where
  obj := intervalPair F j
  map {p q} f := ⟨f.val.val, by
    apply pair_ext
    · apply Subtype.ext
      exact congrArg (fun c : Chart F j q.1 ↦ c.firstCut) f.property
    · apply Subtype.ext
      exact congrArg (fun c : Chart F j q.1 ↦ c.lastCut) f.property⟩
  map_id p := by
    apply CategoryOfElements.ext
    rfl
  map_comp f g := by
    apply CategoryOfElements.ext
    rfl

/-- The unchanged original source under the actual chart endpoints. -/
abbrev base : Index F j ⥤ A := toPairs F j ⋙ JTJointPairSourceDiagram.base F j

/-- Restrict the original native source to each actual adjacent interval. -/
abbrev native : Index F j ⥤ NecklaceCode := toPairs F j ⋙ JTJointPairGapDiagram.native F j

/-- Every actual interval in this full image source has its canonical single-simplex code. -/
def simplexIso (p : Index F j) :
    (native F j).obj p ≅ single (p.2.lastCut.val - p.2.firstCut.val) :=
  chartIso F j p.1 p.2.cuts p.2.firstCut p.2.lastCut p.2.adjacent

/-- The actual adjacent-bead chart functor, including all coalescing original operators. -/
def singleNative : Index F j ⥤ NecklaceCode where
  obj p := single (p.2.lastCut.val - p.2.firstCut.val)
  map {p q} f := (simplexIso F j p).inv ≫ (native F j).map f ≫ (simplexIso F j q).hom
  map_id p := by simp only [(native F j).map_id, Category.id_comp, Iso.inv_hom_id]
  map_comp f g := by simp only [(native F j).map_comp, Category.assoc, Iso.hom_inv_id_assoc]

/-- These chart codes agree naturally with the complete original interval restrictions. -/
def nativeIso : native F j ≅ singleNative F j :=
  NatIso.ofComponents (simplexIso F j) (by
    intro p q f
    change (native F j).map f ≫ (simplexIso F j q).hom =
      (simplexIso F j p).hom ≫
        ((simplexIso F j p).inv ≫ (native F j).map f ≫ (simplexIso F j q).hom)
    simp only [Iso.hom_inv_id_assoc])

/-- Original native inclusions retain every chart endpoint and all original source maps. -/
abbrev inclusions : native F j ⋙ NecklaceCode.simplicialFunctor ⟶
    base F j ⋙ codes L ⋙ NecklaceCode.simplicialFunctor :=
  Functor.whiskerLeft (toPairs F j) (JTJointPairGapDiagram.inclusions F j)

/-- The same full natural inclusion expressed using the single-simplex chart codes. -/
def singleInclusions : singleNative F j ⋙ NecklaceCode.simplicialFunctor ⟶
    base F j ⋙ codes L ⋙ NecklaceCode.simplicialFunctor :=
  Functor.whiskerRight (nativeIso F j).inv NecklaceCode.simplicialFunctor ≫ inclusions F j

end
end DaggerModels.PartII.JTJointSubdivisionBeadCharts
