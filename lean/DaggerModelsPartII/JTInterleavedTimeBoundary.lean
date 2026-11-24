import DaggerModelsPartII.JTInterleavedTimeFace
import DaggerModelsPartII.JTFiniteSubcomplexPreimageGluing
import DaggerModelsPartII.JTSubcomplexRangeUnion

/-!
# The union of all time faces with the original prism
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial MonoidalCategory
open scoped SSet.modelCategoryQuillen

universe u v

namespace DaggerModels.PartII.JTHigherInterleavedParameter

open SSet.Subcomplex

noncomputable section

/-- The enlarged time boundary consists of faces missing at least one
time vertex. -/
def timeBoundary (k n : ℕ) :
    (SSet.stdSimplex.obj (common ⦋k⦌ ⦋n⦌) : SSet.{u}).Subcomplex :=
  Finset.univ.sup (fun a : Fin (n + 1) ↦ timeFace k n (Finset.univ.erase a))

theorem timeBoundary_eq_iSup (k n : ℕ) :
    timeBoundary.{u} k n = ⨆ a : Fin (n + 1), timeFace k n (Finset.univ.erase a) :=
  Finset.sup_univ_eq_iSup _

theorem timeFace_univ (k n : ℕ) : timeFace.{u} k n Finset.univ = ⊤ := by
  ext q x
  induction q using Opposite.rec with
  | op q =>
    induction q using SimplexCategory.rec with
    | _ d =>
      rw [mem_timeFace_iff]
      simp

theorem timeFace_finset_inf (k n : ℕ) {ι : Type v}
    (s : Finset ι) (F : ι → Finset (Fin (n + 1))) :
    timeFace.{u} k n (s.inf F) = s.inf (fun a ↦ timeFace k n (F a)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.inf_empty] using timeFace_univ.{u} k n
  | @insert i s hi ih =>
    simp only [Finset.inf_insert, timeFace_inf, ih]

/-- The full enlarged time boundary is weakly compared to its actual
preimage in the original prism. -/
theorem timeBoundary_fromPreimage_weak (k n : ℕ) :
    WeakEquivalence ((timeBoundary.{u} k n).fromPreimage (prism ⦋k⦌ ⦋n⦌)) := by
  apply JTFiniteSubcomplexPreimageGluing.weak_finset_sup
  intro t _ _
  rw [← timeFace_finset_inf]
  exact timeFaceComparison_weak _ _ _

/-- The inclusion of the union containing the entire prism and enlarged
time boundary is a Kan trivial cofibration. -/
theorem prismTimeBoundary_weak (k n : ℕ) :
    WeakEquivalence (JTSubcomplexRangeUnion.union
      (prism.{u} ⦋k⦌ ⦋n⦌) (timeBoundary k n)).ι := by
  haveI := prism_weak.{u} ⦋k⦌ ⦋n⦌
  exact JTSubcomplexRangeUnion.union_weak _ _ (timeBoundary_fromPreimage_weak k n)

/-- Pulling the enlarged time boundary back to the product prism
recovers the product with the ordinary time boundary. -/
theorem timeBoundary_preimage (k n : ℕ) :
    (timeBoundary.{u} k n).preimage (prism ⦋k⦌ ⦋n⦌) =
      range ((Δ[k] : SSet.{u}) ◁ (SSet.boundary n).ι) := by
  rw [show ((Δ[k] : SSet.{u}) ◁ (SSet.boundary n).ι) =
      (𝟙 (Δ[k] : SSet.{u})) ⊗ₘ (SSet.boundary n).ι from rfl,
    SSet.Subcomplex.range_tensorHom, range_eq_top]
  have hR : SSet.Subcomplex.range (SSet.boundary.{u} n).ι = SSet.boundary n :=
    SSet.Subcomplex.range_ι _
  rw [hR]
  ext q x
  induction q using Opposite.rec with
  | op q =>
    induction q using SimplexCategory.rec with
    | _ d =>
      rw [timeBoundary_eq_iSup, preimage_iSup]
      change x ∈ (⨆ a : Fin (n + 1), (timeFace k n (Finset.univ.erase a)).preimage
        (prism ⦋k⦌ ⦋n⦌)).obj (op ⦋d⦌) ↔
        x.1 ∈ (⊤ : (Δ[k] : SSet.{u}).Subcomplex).obj (op ⦋d⦌) ∧
          x.2 ∈ (SSet.boundary n).obj (op ⦋d⦌)
      rw [Subfunctor.iSup_obj, Set.mem_iUnion]
      simp only [mem_timeFace_preimage_iff, Finset.mem_erase, Finset.mem_univ, and_true,
        Subfunctor.top_obj, Set.top_eq_univ, Set.mem_univ, true_and]
      change (∃ a : Fin (n + 1), ∀ i : Fin (d + 1),
        (SSet.stdSimplex.objEquiv x.2).toOrderHom i ≠ a) ↔
        ¬ Function.Surjective (SSet.stdSimplex.objEquiv x.2).toOrderHom
      simp only [Function.Surjective, not_forall, not_exists, SimplexCategory.len_mk, ne_eq]

end

end DaggerModels.PartII.JTHigherInterleavedParameter
