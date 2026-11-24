import DaggerModelsPartII.JTFiniteCoefficientBridgePrism
import NativeIhomRelativeSectionsWeak

/-!
# Exact simplicial overlaps for finitely many coefficient sides
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial
open MonoidalCategory CartesianMonoidalCategory
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.JTFiniteCoefficientBridgeOverlap

open JTFiniteCoefficientBridgeOrder JTFiniteCoefficientBridgeTime
open JTFiniteCoefficientBridgePrism
open SSet.Subcomplex

noncomputable section

private abbrev simplex (k : SimplexCategory) := SSet.stdSimplex.{u}.obj k

theorem range_stdMap_iff {a b : SimplexCategory} (j : a ⟶ b)
    (hj : Function.Injective j.toOrderHom) (q : SimplexCategoryᵒᵖ)
    (z : (simplex.{u} b).obj q) :
    z ∈ (range (SSet.stdSimplex.map j)).obj q ↔
      ∀ v, (SSet.stdSimplex.objEquiv z).toOrderHom v ∈ Set.range j.toOrderHom := by
  constructor
  · rintro ⟨x, rfl⟩ v
    exact ⟨(SSet.stdSimplex.objEquiv x).toOrderHom v, rfl⟩
  · intro H
    choose f hf using H
    let g : q.unop ⟶ a := SimplexCategory.Hom.mk ⟨f, by
      intro v w hvw
      apply (j.toOrderHom.monotone.strictMono_of_injective hj).le_iff_le.mp
      rw [hf, hf]
      exact (SSet.stdSimplex.objEquiv z).toOrderHom.monotone hvw⟩
    refine ⟨SSet.stdSimplex.objEquiv.symm g, SSet.stdSimplex.objEquiv.injective ?_⟩
    ext v : 3
    change j.toOrderHom
      ((SSet.stdSimplex.objEquiv.{u} (SSet.stdSimplex.objEquiv.symm g)).toOrderHom v) = _
    rw [Equiv.apply_symm_apply]
    exact hf v

variable {k b' : SimplexCategory} {m : ℕ} {b : Fin (m + 1) → SimplexCategory}
    (c : ∀ e : Fin (m + 1), k ⟶ b e) (u : k ⟶ b')
    (h : ∀ e, b e ⟶ b') (hu : ∀ e, c e ≫ h e = u) (n : SimplexCategory)

instance side_mono (e : Fin (m + 1)) : Mono (side c u h hu n e) :=
  SimplexCategory.mono_iff_injective.mpr (side_injective c u h hu n e)

abbrev sideRange (e : Fin (m + 1)) : (simplex.{u} (bridge k n m)).Subcomplex :=
  range (SSet.stdSimplex.map (side c u h hu n e))

private theorem mem_sideVertexRange (e : Fin (m + 1))
    (v : Fin ((bridge k n m).len + 1)) :
    v ∈ Set.range (side c u h hu n e).toOrderHom ↔
      ((vertexEquiv c u n).symm v).2 = e := by
  obtain ⟨x, rfl⟩ := (vertexEquiv c u n).surjective v
  rw [Equiv.symm_apply_apply]
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨y, rfl⟩ := (JTCommonCoefficientParameter.vertexEquiv (c e) n).surjective v
    rw [side_vertexEquiv] at hv
    exact (congrArg Prod.snd ((vertexEquiv c u n).injective hv)).symm
  · intro hx
    refine ⟨JTCommonCoefficientParameter.vertexEquiv (c e) n x.1, ?_⟩
    rw [side_vertexEquiv, ← hx]
    rfl

private theorem mem_timeVertexRange (e : Fin (m + 1))
    (v : Fin ((time m n).len + 1)) :
    v ∈ Set.range (timeSide n e).toOrderHom ↔
      ((timeVertexEquiv m n).symm v).1 = e := by
  obtain ⟨x, rfl⟩ := (timeVertexEquiv m n).surjective v
  rw [Equiv.symm_apply_apply]
  constructor
  · rintro ⟨t, ht⟩
    exact (congrArg Prod.fst ((timeVertexEquiv m n).injective ht)).symm
  · intro hx
    refine ⟨x.2, ?_⟩
    change timeVertexEquiv m n (e, x.2) = timeVertexEquiv m n x
    rw [← hx]

theorem side_disjoint : Pairwise fun e e' : Fin (m + 1) ↦
    sideRange.{u} c u h hu n e ⊓ sideRange c u h hu n e' = ⊥ := by
  intro e e' he
  ext q z
  constructor
  · intro hz
    change z ∈ (sideRange c u h hu n e).obj q ∧
      z ∈ (sideRange c u h hu n e').obj q at hz
    have H (j : Fin (m + 1)) (hj : z ∈ (sideRange c u h hu n j).obj q) :=
      (mem_sideVertexRange c u h hu n j _).1
        ((range_stdMap_iff (side c u h hu n j) (side_injective c u h hu n j) q z).1 hj 0)
    exact (he ((H e hz.1).symm.trans (H e' hz.2))).elim
  · exact False.elim

theorem side_preimage_range (e : Fin (m + 1)) :
    range (simplex.{u} k ◁ SSet.stdSimplex.map (timeSide n e)) =
      (sideRange c u h hu n e).preimage (prism c u n) := by
  rw [show (simplex.{u} k ◁ SSet.stdSimplex.map (timeSide n e)) =
      (𝟙 (simplex k)) ⊗ₘ SSet.stdSimplex.map (timeSide n e) from rfl,
    range_tensorHom, range_eq_top]
  ext q x
  change (x.1 ∈ (⊤ : (simplex.{u} k).Subcomplex).obj q ∧
      x.2 ∈ (range (SSet.stdSimplex.map (timeSide n e))).obj q) ↔
    (prism c u n).app q x ∈ (sideRange c u h hu n e).obj q
  simp only [Subfunctor.top_obj, Set.top_eq_univ, Set.mem_univ, true_and,
    range_stdMap_iff _ (timeSide_injective n e),
    range_stdMap_iff _ (side_injective c u h hu n e),
    mem_sideVertexRange, mem_timeVertexRange, prism_app, rankVertex,
    Equiv.symm_apply_apply]

/-- The exact overlap is represented by the original ordinary prism. -/
def sidePreimageIso (e : Fin (m + 1)) :
    (simplex.{u} k ⊗ simplex n) ≅
      ((sideRange c u h hu n e).preimage (prism c u n)).toSSet := by
  haveI := JTHigherInterleavedParameter.stdSimplex_map_mono_of_mono.{u} (timeSide n e)
  haveI := DaggerNativeIhomRelativeSectionsWeak.left_tensor_mono
    (simplex.{u} k) (SSet.stdSimplex.map (timeSide n e))
  exact asIso (toRange (simplex.{u} k ◁ SSet.stdSimplex.map (timeSide n e))) ≪≫
    SSet.Subcomplex.eqToIso (side_preimage_range c u h hu n e)

@[reassoc]
theorem sidePreimageIso_ι (e : Fin (m + 1)) :
    (sidePreimageIso.{u} c u h hu n e).hom ≫
      ((sideRange c u h hu n e).preimage (prism c u n)).ι =
      simplex k ◁ SSet.stdSimplex.map (timeSide n e) := by
  simp [sidePreimageIso, Category.assoc]

theorem sidePreimageIso_compare (e : Fin (m + 1)) :
    (sidePreimageIso.{u} c u h hu n e).hom ≫
      (sideRange c u h hu n e).fromPreimage (prism c u n) =
      JTCommonCoefficientParameter.prism (c e) n ≫
        toRange (SSet.stdSimplex.map (side c u h hu n e)) := by
  rw [← cancel_mono (sideRange c u h hu n e).ι]
  calc
    _ = ((sidePreimageIso.{u} c u h hu n e).hom ≫
          ((sideRange c u h hu n e).preimage (prism c u n)).ι) ≫ prism c u n := by
      simp only [Category.assoc, fromPreimage_ι]
    _ = _ := by
      rw [sidePreimageIso_ι, JTFiniteCoefficientBridgePrism.prism_side c u n h hu e]
      simp only [Category.assoc, toRange_ι]

theorem sideComparison_weak (e : Fin (m + 1)) :
    WeakEquivalence ((sideRange.{u} c u h hu n e).fromPreimage (prism c u n)) := by
  haveI := JTHigherInterleavedParameter.stdSimplex_map_mono_of_mono.{u}
    (side c u h hu n e)
  haveI := JTCommonCoefficientParameter.prism_weak.{u} (c e) n
  exact weakEquivalence_of_precomp_of_fac (sidePreimageIso_compare.{u} c u h hu n e)

end

end DaggerModels.PartII.JTFiniteCoefficientBridgeOverlap
