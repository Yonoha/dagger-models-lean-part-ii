import DaggerModelsPartII.JTFiniteCoefficientBridgeReindex
import DaggerModelsPartII.JTFiniteCoefficientBridgeOverlap

/-!
# Exact intersections with the full prism for whole copy subcollections
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open MonoidalCategory CartesianMonoidalCategory
open scoped SSet.modelCategoryQuillen

universe v

namespace DaggerModels.PartII.JTFiniteCoefficientBridgeSubcollection

open JTFiniteCoefficientBridgeOrder (bridge vertexEquiv mapCopies_vertexEquiv)
open JTFiniteCoefficientBridgeTime (time timeVertexEquiv mapCopies_vertex)
open JTFiniteCoefficientBridgePrism JTFiniteCoefficientBridgeReindex
open JTFiniteCoefficientBridgeOverlap (range_stdMap_iff)
open SSet.Subcomplex

noncomputable section

private abbrev simplex (a : SimplexCategory) := SSet.stdSimplex.{v}.obj a

variable {m m' : ℕ} {k b' : SimplexCategory}
variable {b : Fin (m + 1) → SimplexCategory} {b₂ : Fin (m' + 1) → SimplexCategory}
variable (c : ∀ e, k ⟶ b e) (d : ∀ e, k ⟶ b₂ e) (u : k ⟶ b') (n : SimplexCategory)
variable (j : ⦋m⦌ ⟶ ⦋m'⦌) (hj : Function.Injective j.toOrderHom)
variable (hr : ∀ (e : Fin (m + 1)) (x : Fin (k.len + 1) × Fin (n.len + 1)),
  JTCommonCoefficientParameter.vertexEquiv (c e) n x =
    JTCommonCoefficientParameter.vertexEquiv (d (j.toOrderHom e)) n x)

abbrev coefficientOperator := JTFiniteCoefficientBridgeOrder.mapCopies c d u n j hj hr
abbrev timeOperator := JTFiniteCoefficientBridgeTime.mapCopies j hj n

theorem coefficientOperator_injective :
    Function.Injective (coefficientOperator c d u n j hj hr).toOrderHom := by
  intro a b hab
  obtain ⟨x, rfl⟩ := (vertexEquiv c u n).surjective a
  obtain ⟨y, rfl⟩ := (vertexEquiv c u n).surjective b
  change (JTFiniteCoefficientBridgeOrder.mapCopies c d u n j hj hr).toOrderHom
      (vertexEquiv c u n x) =
    (JTFiniteCoefficientBridgeOrder.mapCopies c d u n j hj hr).toOrderHom
      (vertexEquiv c u n y) at hab
  rw [mapCopies_vertexEquiv, mapCopies_vertexEquiv] at hab
  have H := (vertexEquiv d u n).injective hab
  have h₁ := congrArg Prod.fst H
  have ht := congrArg Prod.snd H
  have h₂ : x.2 = y.2 := hj ht
  exact congrArg (vertexEquiv c u n) (Prod.ext h₁ h₂)

theorem timeOperator_injective : Function.Injective (timeOperator n j hj).toOrderHom := by
  intro a b hab
  obtain ⟨x, rfl⟩ := (timeVertexEquiv m n).surjective a
  obtain ⟨y, rfl⟩ := (timeVertexEquiv m n).surjective b
  change (JTFiniteCoefficientBridgeTime.mapCopies j hj n).toOrderHom (timeVertexEquiv m n x) =
    (JTFiniteCoefficientBridgeTime.mapCopies j hj n).toOrderHom (timeVertexEquiv m n y) at hab
  rw [mapCopies_vertex, mapCopies_vertex] at hab
  have H := (timeVertexEquiv m' n).injective hab
  have ht := congrArg Prod.fst H
  have h₁ : x.1 = y.1 := hj ht
  have h₂ := congrArg Prod.snd H
  exact congrArg (timeVertexEquiv m n) (Prod.ext h₁ h₂)

private theorem rankVertex_surjective : Function.Surjective (rankVertex c u n) := by
  intro a
  obtain ⟨⟨⟨v, t⟩, e⟩, rfl⟩ := (vertexEquiv c u n).surjective a
  exact ⟨(v, timeVertexEquiv m n (e, t)), rankVertex_apply c u n v e t⟩

theorem mem_rankVertex_range_iff (a : Fin (k.len + 1)) (t : Fin ((time m' n).len + 1)) :
    rankVertex d u n (a, t) ∈ Set.range (coefficientOperator c d u n j hj hr).toOrderHom ↔
      t ∈ Set.range (timeOperator n j hj).toOrderHom := by
  constructor
  · rintro ⟨r, h⟩
    obtain ⟨⟨a', t'⟩, rfl⟩ := rankVertex_surjective c u n r
    have H := rankVertex_mapCopies c d u n j hj hr a' t'
    exact ⟨t', congrArg Prod.snd (rankVertex_injective d u n (H.symm.trans h))⟩
  · rintro ⟨t', rfl⟩
    exact ⟨rankVertex c u n (a, t'), rankVertex_mapCopies c d u n j hj hr a t'⟩

abbrev subcollectionRange : (simplex.{v} (bridge k n m')).Subcomplex :=
  range (SSet.stdSimplex.map (coefficientOperator c d u n j hj hr))

/-- Pulling an entire subcollection back to the full prism gives its
entire time subcollection times the original coefficient simplex. -/
theorem subcollection_preimage_range :
    range (simplex.{v} k ◁ SSet.stdSimplex.map (timeOperator n j hj)) =
      (subcollectionRange.{v} c d u n j hj hr).preimage (prism d u n) := by
  rw [show (simplex.{v} k ◁ SSet.stdSimplex.map (timeOperator n j hj)) =
      (𝟙 (simplex k)) ⊗ₘ SSet.stdSimplex.map (timeOperator n j hj) from rfl,
    range_tensorHom, range_eq_top]
  ext q x
  change (x.1 ∈ (⊤ : (simplex.{v} k).Subcomplex).obj q ∧
      x.2 ∈ (range (SSet.stdSimplex.map (timeOperator n j hj))).obj q) ↔
    (prism d u n).app q x ∈ (subcollectionRange.{v} c d u n j hj hr).obj q
  simp only [Subfunctor.top_obj, Set.top_eq_univ, Set.mem_univ, true_and,
    range_stdMap_iff _ (timeOperator_injective n j hj),
    range_stdMap_iff _ (coefficientOperator_injective c d u n j hj hr),
    prism_app, mem_rankVertex_range_iff c d u n j hj hr]

instance coefficientOperator_mono : Mono (coefficientOperator c d u n j hj hr) :=
  SimplexCategory.mono_iff_injective.mpr (coefficientOperator_injective c d u n j hj hr)

instance timeOperator_mono : Mono (timeOperator n j hj) :=
  SimplexCategory.mono_iff_injective.mpr (timeOperator_injective n j hj)

/-- The smaller full product represents this entire overlap. -/
def subcollectionPreimageIso :
    simplex.{v} k ⊗ simplex (time m n) ≅
      ((subcollectionRange.{v} c d u n j hj hr).preimage (prism d u n)).toSSet := by
  haveI := JTHigherInterleavedParameter.stdSimplex_map_mono_of_mono.{v} (timeOperator n j hj)
  haveI := DaggerNativeIhomRelativeSectionsWeak.left_tensor_mono
    (simplex.{v} k) (SSet.stdSimplex.map (timeOperator n j hj))
  exact asIso (toRange (simplex.{v} k ◁ SSet.stdSimplex.map (timeOperator n j hj))) ≪≫
    SSet.Subcomplex.eqToIso (subcollection_preimage_range c d u n j hj hr)

theorem subcollectionPreimageIso_ι :
    (subcollectionPreimageIso.{v} c d u n j hj hr).hom ≫
      ((subcollectionRange c d u n j hj hr).preimage (prism d u n)).ι =
      simplex k ◁ SSet.stdSimplex.map (timeOperator n j hj) := by
  simp [subcollectionPreimageIso, Category.assoc]

theorem subcollectionPreimageIso_compare :
    (subcollectionPreimageIso.{v} c d u n j hj hr).hom ≫
      (subcollectionRange c d u n j hj hr).fromPreimage (prism d u n) =
      prism c u n ≫ toRange (SSet.stdSimplex.map (coefficientOperator c d u n j hj hr)) := by
  rw [← cancel_mono (subcollectionRange.{v} c d u n j hj hr).ι]
  calc
    _ = ((subcollectionPreimageIso.{v} c d u n j hj hr).hom ≫
        ((subcollectionRange c d u n j hj hr).preimage (prism d u n)).ι) ≫ prism d u n := by
      simp only [Category.assoc, fromPreimage_ι]
    _ = _ := by
      rw [subcollectionPreimageIso_ι, ← prism_mapCopies c d u n j hj hr]
      simp only [Category.assoc, toRange_ι]

/-- Every entire nonempty subcollection has weak preimage comparison. -/
theorem subcollectionComparison_weak :
    WeakEquivalence ((subcollectionRange.{v} c d u n j hj hr).fromPreimage (prism d u n)) := by
  haveI := JTHigherInterleavedParameter.stdSimplex_map_mono_of_mono.{v}
    (coefficientOperator c d u n j hj hr)
  haveI := prism_weak.{v} c u n
  exact weakEquivalence_of_precomp_of_fac (subcollectionPreimageIso_compare.{v} c d u n j hj hr)

end

end DaggerModels.PartII.JTFiniteCoefficientBridgeSubcollection
