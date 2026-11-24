import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Data.Finset.Sort

/-! The full inverse image of a nonempty ordinal face along an ordinal surjection. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Simplicial

namespace DaggerModels.PartII.JTOrdinalFaceInverseImage

noncomputable section

variable {s k d : SimplexCategory} (u : s ⟶ k) (α : d ⟶ k)

/-- Every coefficient vertex whose original image belongs to the given face. -/
def vertices : Finset (Fin (d.len + 1)) := by
  classical
  exact Finset.univ.filter (fun v ↦ α.toOrderHom v ∈ Set.range u.toOrderHom)

@[simp] theorem mem_vertices (v : Fin (d.len + 1)) :
    v ∈ vertices u α ↔ ∃ a, u.toOrderHom a = α.toOrderHom v := by
  classical
  simp only [vertices, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_range]

/-- Its coefficient ordinal lists the full preimage in the inherited order. -/
def ordinal : SimplexCategory := ⦋(vertices u α).card - 1⦌

variable (hα : Function.Surjective α.toOrderHom)

include hα in
private theorem nonempty_vertices : (vertices u α).Nonempty := by
  obtain ⟨v, hv⟩ := hα (u.toOrderHom 0)
  exact ⟨v, (mem_vertices u α v).mpr ⟨0, hv.symm⟩⟩

include hα in
private theorem card_vertices : (vertices u α).card = (ordinal u α).len + 1 := by
  have hpos := Finset.card_pos.mpr (nonempty_vertices u α hα)
  dsimp only [ordinal, SimplexCategory.len_mk]
  omega

/-- The increasing enumeration of the full inverse-image face. -/
def enumerate : Fin ((ordinal u α).len + 1) ≃o vertices u α :=
  (vertices u α).orderIsoOfFin (card_vertices u α hα)

/-- The literal inclusion of the full inverse image in the new coefficient ordinal. -/
def incl : ordinal u α ⟶ d :=
  SimplexCategory.Hom.mk ⟨fun v ↦ (enumerate u α hα v).val, (enumerate u α hα).monotone⟩

theorem incl_injective : Function.Injective (incl u α hα).toOrderHom := by
  intro a b h
  exact (enumerate u α hα).injective (Subtype.ext h)

theorem incl_mono : Mono (incl u α hα) :=
  SimplexCategory.mono_iff_injective.mpr (incl_injective u α hα)

private def chosen (v : vertices u α) : Fin (s.len + 1) :=
  Classical.choose ((mem_vertices u α v.val).mp v.property)

private theorem chosen_spec (v : vertices u α) :
    u.toOrderHom (chosen u α v) = α.toOrderHom v.val :=
  Classical.choose_spec ((mem_vertices u α v.val).mp v.property)

variable (hu : Function.Injective u.toOrderHom)

/-- The full new face maps to the exact old face, retaining every coefficient value. -/
def toFace : ordinal u α ⟶ s :=
  SimplexCategory.Hom.mk ⟨fun v ↦ chosen u α (enumerate u α hα v), by
    intro a b hab
    have hstrict : StrictMono u.toOrderHom :=
      (u.toOrderHom.monotone.strictMono_iff_injective).mpr hu
    apply hstrict.le_iff_le.mp
    rw [chosen_spec, chosen_spec]
    exact α.toOrderHom.monotone ((enumerate u α hα).monotone hab)⟩

/-- The inverse-image square commutes as a literal equality of ordinal maps. -/
theorem toFace_fac : toFace u α hα hu ≫ u = incl u α hα ≫ α := by
  ext v : 3
  exact chosen_spec u α (enumerate u α hα v)

variable {e : SimplexCategory} (v : e ⟶ d) (b : e ⟶ s)
variable (h : v ≫ α = b ≫ u)

include b h in
private theorem lift_mem (a : Fin (e.len + 1)) : v.toOrderHom a ∈ vertices u α := by
  apply (mem_vertices u α _).mpr
  exact ⟨b.toOrderHom a, (SimplexCategory.congr_toOrderHom_apply h a).symm⟩

/-- Every ordinal map with image in the old face factors through the full preimage. -/
def lift : e ⟶ ordinal u α :=
  SimplexCategory.Hom.mk ⟨fun a ↦ (enumerate u α hα).symm
    ⟨v.toOrderHom a, lift_mem u α v b h a⟩,
    fun _ _ hab ↦ (enumerate u α hα).symm.monotone (v.toOrderHom.monotone hab)⟩

/-- The factor recovers the entire new coefficient map. -/
theorem lift_incl : lift u α hα v b h ≫ incl u α hα = v := by
  ext a : 3
  exact congrArg Subtype.val ((enumerate u α hα).apply_symm_apply _)

/-- The factor recovers the original face coordinate, without any choices of sections. -/
theorem lift_toFace : lift u α hα v b h ≫ toFace u α hα hu = b := by
  haveI : Mono u := SimplexCategory.mono_iff_injective.mpr hu
  apply (cancel_mono u).mp
  rw [Category.assoc, toFace_fac, ← Category.assoc, lift_incl]
  exact h

end
end DaggerModels.PartII.JTOrdinalFaceInverseImage
