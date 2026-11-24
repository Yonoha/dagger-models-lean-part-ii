import DaggerModelsPartII.JTJointPairSourceDiagram
import DaggerModelsPartII.GrothendieckContractibleFibers

/-!
Actual subdivisions of an ordered pair of cuts above one fixed target joint.
Every subdivision contains both cuts and every native joint between them.
Original pair arrows act by their literal vertex images; refinement arrows
are inclusions of cut sets. The resulting weak projection lands in the exact
pair category, with no weakness assertion about its map to the original base.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerOriginalProductGadget DaggerSSetGluing DaggerNerveHomotopy
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTJointPairSubdivisionDiagram

open JTParametrizedTargetFamilies (Family codes)
open JTTargetJointMarks (Joint)
open JTProjectiveOrderedFiberComparison (row)

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
private abbrev left (p : E F j) := p.2.left.val
private abbrev right (p : E F j) := p.2.right.val

/-- The complete cut condition, including all original native joints in the interval. -/
def Admissible (p : E F j) (C : Finset (Fin ((T F j p).len + 1))) : Prop :=
  left F j p ∈ C ∧ right F j p ∈ C ∧
    (∀ v ∈ C, left F j p ≤ v ∧ v ≤ right F j p) ∧
    (∀ v ∈ (T F j p).joints, left F j p ≤ v → v ≤ right F j p → v ∈ C)

/-- Subdivisions are ordered by refinement, so every inclusion remains an actual arrow. -/
abbrev Subdivision (p : E F j) :=
  {C : Finset (Fin ((T F j p).len + 1)) // Admissible F j p C}

/-- The full vertex interval is the greatest admissible subdivision, also at a zero gap. -/
def greatest (p : E F j) : Subdivision F j p :=
  ⟨Finset.Icc (left F j p) (right F j p), by
    refine ⟨Finset.mem_Icc.mpr ⟨le_rfl, p.2.le⟩,
      Finset.mem_Icc.mpr ⟨p.2.le, le_rfl⟩, ?_, ?_⟩
    · intro v hv
      exact Finset.mem_Icc.mp hv
    · intro v _ hl hr
      exact Finset.mem_Icc.mpr ⟨hl, hr⟩⟩

/-- Every cut set refines to the full original vertex interval. -/
theorem le_greatest (p : E F j) (C : Subdivision F j p) : C ≤ greatest F j p := by
  intro v hv
  exact Finset.mem_Icc.mpr (C.property.2.2.1 v hv)

/-- The refinement category has an actual terminal object in every exact pair fiber. -/
def greatestIsTerminal (p : E F j) : IsTerminal (greatest F j p) :=
  IsTerminal.ofUniqueHom (fun C ↦ homOfLE (le_greatest F j p C))
    (fun _ _ ↦ Subsingleton.elim _ _)

private abbrev vertices {p q : E F j} (f : p ⟶ q) :=
  orderMap ((codes L).map f.val).map

private theorem vertices_left {p q : E F j} (f : p ⟶ q) :
    vertices F j f (left F j p) = left F j q :=
  JTJointPairSourceDiagram.left_map F j f

private theorem vertices_right {p q : E F j} (f : p ⟶ q) :
    vertices F j f (right F j p) = right F j q :=
  JTJointPairSourceDiagram.right_map F j f

/-- The literal vertex image of a subdivision is admissible under every original pair arrow.
Interior target joints have source-joint preimages inside the original cut interval. -/
theorem image_admissible {p q : E F j} (f : p ⟶ q) (C : Subdivision F j p) :
    Admissible F j q (C.val.image (vertices F j f)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨left F j p, C.property.1, vertices_left F j f⟩
  · exact Finset.mem_image.mpr ⟨right F j p, C.property.2.1, vertices_right F j f⟩
  · intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hl, hr⟩ := C.property.2.2.1 u hu
    constructor
    · simpa only [vertices_left F j f] using (vertices F j f).monotone hl
    · simpa only [vertices_right F j f] using (vertices F j f).monotone hr
  · intro v hv hl hr
    by_cases he : v = left F j q
    · exact Finset.mem_image.mpr
        ⟨left F j p, C.property.1, (vertices_left F j f).trans he.symm⟩
    by_cases he' : v = right F j q
    · exact Finset.mem_image.mpr
        ⟨right F j p, C.property.2.1, (vertices_right F j f).trans he'.symm⟩
    have hvl : left F j q < v := lt_of_le_of_ne hl (Ne.symm he)
    have hvr : v < right F j q := lt_of_le_of_ne hr he'
    obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp
      (joints_subset_image ((codes L).map f.val) hv)
    have hul : left F j p ≤ u := by
      by_contra hn
      have hh := (vertices F j f).monotone (le_of_lt (lt_of_not_ge hn))
      rw [vertices_left F j f, huv] at hh
      exact (not_le_of_gt hvl) hh
    have hur : u ≤ right F j p := by
      by_contra hn
      have hh := (vertices F j f).monotone (le_of_lt (lt_of_not_ge hn))
      rw [vertices_right F j f, huv] at hh
      exact (not_le_of_gt hvr) hh
    exact Finset.mem_image.mpr ⟨u, C.property.2.2.2 u hu hul hur, huv⟩

/-- Transport retains precisely the image cut set, including coalescing cuts. -/
def transport {p q : E F j} (f : p ⟶ q) (C : Subdivision F j p) :
    Subdivision F j q :=
  ⟨C.val.image (vertices F j f), image_admissible F j f C⟩

/-- Original native maps preserve every refinement inclusion. -/
theorem transport_monotone {p q : E F j} (f : p ⟶ q) :
    Monotone (transport F j f) := by
  intro C D h
  exact Finset.image_subset_image h

private theorem vertices_id (p : E F j) (v : Fin ((T F j p).len + 1)) :
    vertices F j (𝟙 p) v = v := by
  change orderMap ((codes L).map (𝟙 p.1)).map v = v
  rw [(codes L).map_id]
  change ((T F j p).verticesEquiv
    ((T F j p).verticesEquiv.symm (ULift.up v))).down = v
  rw [(T F j p).verticesEquiv.apply_symm_apply]

private theorem vertices_comp {p q r : E F j} (f : p ⟶ q) (g : q ⟶ r)
    (v : Fin ((T F j p).len + 1)) :
    vertices F j (f ≫ g) v = vertices F j g (vertices F j f v) := by
  change orderMap ((codes L).map (f.val ≫ g.val)).map v = _
  rw [(codes L).map_comp]
  exact orderMap_comp_apply ((codes L).map f.val).map ((codes L).map g.val).map v

/-- Identity transport preserves the exact subdivision. -/
theorem transport_id (p : E F j) (C : Subdivision F j p) :
    transport F j (𝟙 p) C = C := by
  apply Subtype.ext
  change C.val.image (vertices F j (𝟙 p)) = C.val
  rw [show (vertices F j (𝟙 p) : _ → _) = id from funext (vertices_id F j p)]
  exact Finset.image_id

/-- Native images compose strictly, including degeneracies and collapsed intervals. -/
theorem transport_comp {p q r : E F j} (f : p ⟶ q) (g : q ⟶ r)
    (C : Subdivision F j p) :
    transport F j (f ≫ g) C = transport F j g (transport F j f C) := by
  apply Subtype.ext
  change C.val.image (vertices F j (f ≫ g)) =
    (C.val.image (vertices F j f)).image (vertices F j g)
  rw [Finset.image_image]
  congr 1
  exact funext (vertices_comp F j f g)

private theorem preorder_functor_ext {B C : Type} [SmallCategory B] [Preorder C]
    {G H : B ⥤ C} (h : ∀ b, G.obj b = H.obj b) : G = H := by
  refine CategoryTheory.Functor.ext h ?_
  intros
  exact Subsingleton.elim _ _

/-- The complete diagram of actual cut subdivisions and refinement arrows. -/
def diagram : E F j ⥤ Cat.{0, 0} where
  obj p := Cat.of (Subdivision F j p)
  map f := (transport_monotone F j f).functor.toCatHom
  map_id p := by
    apply Cat.Hom.ext
    exact preorder_functor_ext (B := Subdivision F j p) (C := Subdivision F j p)
      (transport_id F j p)
  map_comp {p q r} f g := by
    apply Cat.Hom.ext
    exact preorder_functor_ext (B := Subdivision F j p) (C := Subdivision F j r)
      (transport_comp F j f g)

/-- Objects retain the exact original pair; arrows also retain genuine refinements. -/
abbrev Index := Grothendieck (diagram F j)

/-- Forget the subdivision without changing either original cut or its native transport. -/
abbrev projection : Index F j ⥤ E F j := Grothendieck.forget (diagram F j)

/-- A literal refinement gives a vertical arrow over the unchanged exact pair. -/
def refinement (p : E F j) (C D : Subdivision F j p) (h : C ≤ D) :
    (⟨p, C⟩ : Index F j) ⟶ ⟨p, D⟩ :=
  (Grothendieck.ι (diagram F j) p).map (homOfLE h : C ⟶ D)

/-- Refining cuts does not change the original source arrow or either marked endpoint. -/
theorem refinement_base (p : E F j) (C D : Subdivision F j p) (h : C ≤ D) :
    (refinement F j p C D h).base = 𝟙 p := rfl

/-- Every refinement fiber has weakly contractible nerve by its actual greatest cut set. -/
theorem subdivision_point_GW (p : E F j) :
    GW (pointMap (nerve (Subdivision F j p))) := by
  let C := Subdivision F j p
  let q : C ⥤ Discrete PUnit := (Functor.const _).obj ⟨PUnit.unit⟩
  let s : Discrete PUnit ⥤ C := (Functor.const _).obj (greatest F j p)
  let η : 𝟭 C ⟶ q ⋙ s :=
    { app := (greatestIsTerminal F j p).from
      naturality := fun {_ _} _ ↦ Subsingleton.elim _ _ }
  let ε : s ⋙ q ⟶ 𝟭 (Discrete PUnit) :=
    { app := fun _ ↦ eqToHom (Subsingleton.elim _ _)
      naturality := fun {_ _} _ ↦ Subsingleton.elim _ _ }
  haveI : WeakEquivalence (nerveMap q) := (weakEquivalence_iff_GW _).mpr
    (nerveMap_geometricW q s (.symm _ _ (.rel _ _ ⟨η⟩)) (.rel _ _ ⟨ε⟩))
  have h : nerveMap q ≫
      (DaggerOriginalFlagFlankification.nerveDiscreteIso PUnit).hom =
        pointMap (nerve C) := pointIsTerminal.hom_ext _ _
  apply (weakEquivalence_iff_GW _).mp
  rw [← h]
  infer_instance

/-- Subdivisions weakly cover the exact pair category. No original-base weakness is asserted. -/
theorem projection_weak : WeakEquivalence (nerveMap (projection F j)) :=
  GrothendieckContractibleFibers.projection_weak (diagram F j)
    (subdivision_point_GW F j)

end
end DaggerModels.PartII.JTJointPairSubdivisionDiagram
