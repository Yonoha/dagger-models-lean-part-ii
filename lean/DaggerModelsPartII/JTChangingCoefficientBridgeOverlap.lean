import DaggerModelsPartII.JTChangingCoefficientBridgePrism
import NativeIhomRelativeSectionsWeak

/-!
# Exact simplicial overlaps for a change of coefficient
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial
open MonoidalCategory CartesianMonoidalCategory
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.JTChangingCoefficientBridgeOverlap

open JTChangingCoefficientBridgeOrder JTChangingCoefficientBridgeTime
open JTChangingCoefficientBridgePrism
open SSet.Subcomplex

noncomputable section

private abbrev simplex (k : SimplexCategory) := SSet.stdSimplex.{u}.obj k

private theorem range_stdMap_iff {a b : SimplexCategory} (j : a ⟶ b)
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

variable {k b b' : SimplexCategory} (c : k ⟶ b) (h : b ⟶ b') (n : SimplexCategory)

instance side_mono (e : Fin 2) : Mono (side c h n e) :=
  SimplexCategory.mono_iff_injective.mpr (side_injective c h n e)

abbrev sideRange (e : Fin 2) : (simplex.{u} (bridge k n)).Subcomplex :=
  range (SSet.stdSimplex.map (side c h n e))

private theorem mem_sideVertexRange (e : Fin 2) (v : Fin ((bridge k n).len + 1)) :
    v ∈ Set.range (side c h n e).toOrderHom ↔
      ((vertexEquiv c h n).symm v).2 = e := by
  obtain ⟨x, rfl⟩ := (vertexEquiv c h n).surjective v
  rw [Equiv.symm_apply_apply]
  fin_cases e
  · change _ ∈ Set.range (side c h n 0).toOrderHom ↔ x.2 = 0
    constructor
    · rintro ⟨v, hv⟩
      obtain ⟨y, rfl⟩ := (JTCommonCoefficientParameter.vertexEquiv c n).surjective v
      rw [side_vertexEquiv_zero] at hv
      exact (congrArg Prod.snd ((vertexEquiv c h n).injective hv)).symm
    · intro hx
      refine ⟨JTCommonCoefficientParameter.vertexEquiv c n x.1, ?_⟩
      rw [side_vertexEquiv_zero, ← hx]
      rfl
  · change _ ∈ Set.range (side c h n 1).toOrderHom ↔ x.2 = 1
    constructor
    · rintro ⟨v, hv⟩
      obtain ⟨y, rfl⟩ := (JTCommonCoefficientParameter.vertexEquiv (c ≫ h) n).surjective v
      rw [side_vertexEquiv_one] at hv
      exact (congrArg Prod.snd ((vertexEquiv c h n).injective hv)).symm
    · intro hx
      refine ⟨JTCommonCoefficientParameter.vertexEquiv (c ≫ h) n x.1, ?_⟩
      rw [side_vertexEquiv_one, ← hx]
      rfl

private theorem mem_timeVertexRange (e : Fin 2) (v : Fin ((time n).len + 1)) :
    v ∈ Set.range (timeSide n e).toOrderHom ↔
      ((timeVertexEquiv n).symm v).1 = e := by
  obtain ⟨x, rfl⟩ := (timeVertexEquiv n).surjective v
  rw [Equiv.symm_apply_apply]
  constructor
  · rintro ⟨t, ht⟩
    exact (congrArg Prod.fst ((timeVertexEquiv n).injective ht)).symm
  · intro hx
    refine ⟨x.2, ?_⟩
    change timeVertexEquiv n (e, x.2) = timeVertexEquiv n x
    rw [← hx]

theorem side_disjoint : sideRange.{u} c h n 0 ⊓ sideRange c h n 1 = ⊥ := by
  ext q z
  constructor
  · intro hz
    change z ∈ (sideRange c h n 0).obj q ∧ z ∈ (sideRange c h n 1).obj q at hz
    have H (e : Fin 2) (he : z ∈ (sideRange c h n e).obj q) :=
      (mem_sideVertexRange c h n e _).1
        ((range_stdMap_iff (side c h n e) (side_injective c h n e) q z).1 he 0)
    exact ((by decide : (0 : Fin 2) ≠ 1) ((H 0 hz.1).symm.trans (H 1 hz.2))).elim
  · exact False.elim

theorem side_preimage_range (e : Fin 2) :
    range (simplex.{u} k ◁ SSet.stdSimplex.map (timeSide n e)) =
      (sideRange c h n e).preimage (prism c h n) := by
  rw [show (simplex.{u} k ◁ SSet.stdSimplex.map (timeSide n e)) =
      (𝟙 (simplex k)) ⊗ₘ SSet.stdSimplex.map (timeSide n e) from rfl,
    range_tensorHom, range_eq_top]
  ext q x
  change (x.1 ∈ (⊤ : (simplex.{u} k).Subcomplex).obj q ∧
      x.2 ∈ (range (SSet.stdSimplex.map (timeSide n e))).obj q) ↔
    (prism c h n).app q x ∈ (sideRange c h n e).obj q
  simp only [Subfunctor.top_obj, Set.top_eq_univ, Set.mem_univ, true_and,
    range_stdMap_iff _ (timeSide_injective n e), range_stdMap_iff _ (side_injective c h n e),
    mem_sideVertexRange, mem_timeVertexRange, prism_app, rankVertex, Equiv.symm_apply_apply]

/-- The exact overlap is represented by the original ordinary prism. -/
def sidePreimageIso (e : Fin 2) :
    (simplex.{u} k ⊗ simplex n) ≅
      ((sideRange c h n e).preimage (prism c h n)).toSSet := by
  haveI := JTHigherInterleavedParameter.stdSimplex_map_mono_of_mono.{u} (timeSide n e)
  haveI := DaggerNativeIhomRelativeSectionsWeak.left_tensor_mono
    (simplex.{u} k) (SSet.stdSimplex.map (timeSide n e))
  exact asIso (toRange (simplex.{u} k ◁ SSet.stdSimplex.map (timeSide n e))) ≪≫
    SSet.Subcomplex.eqToIso (side_preimage_range c h n e)

@[reassoc]
theorem sidePreimageIso_ι (e : Fin 2) :
    (sidePreimageIso.{u} c h n e).hom ≫ ((sideRange c h n e).preimage (prism c h n)).ι =
      simplex k ◁ SSet.stdSimplex.map (timeSide n e) := by
  simp [sidePreimageIso, Category.assoc]

theorem sidePreimageIso_compare (e : Fin 2) :
    (sidePreimageIso.{u} c h n e).hom ≫ (sideRange c h n e).fromPreimage (prism c h n) =
      sidePrism c h n e ≫ toRange (SSet.stdSimplex.map (side c h n e)) := by
  rw [← cancel_mono (sideRange c h n e).ι]
  calc
    _ = ((sidePreimageIso.{u} c h n e).hom ≫
          ((sideRange c h n e).preimage (prism c h n)).ι) ≫ prism c h n := by
      simp only [Category.assoc, fromPreimage_ι]
    _ = _ := by
      rw [sidePreimageIso_ι, prism_side]
      simp only [Category.assoc, toRange_ι]

theorem sideComparison_weak (e : Fin 2) :
    WeakEquivalence ((sideRange.{u} c h n e).fromPreimage (prism c h n)) := by
  haveI := JTHigherInterleavedParameter.stdSimplex_map_mono_of_mono.{u} (side c h n e)
  haveI := sidePrism_weak.{u} c h n e
  exact weakEquivalence_of_precomp_of_fac (sidePreimageIso_compare.{u} c h n e)

abbrev sideUnion : (simplex.{u} (bridge k n)).Subcomplex :=
  sideRange c h n 0 ⊔ sideRange c h n 1

theorem sideUnion_fromPreimage_weak :
    WeakEquivalence ((sideUnion.{u} c h n).fromPreimage (prism c h n)) := by
  apply JTFiniteSubcomplexPreimageGluing.weak_sup
  · exact sideComparison_weak c h n 0
  · exact sideComparison_weak c h n 1
  · rw [side_disjoint]
    let hi : IsInitial (((⊥ : (simplex.{u} (bridge k n)).Subcomplex).preimage
        (prism c h n)) : SSet.{u}) := isInitialBot
    have he : (⊥ : (simplex.{u} (bridge k n)).Subcomplex).fromPreimage (prism c h n) =
        (hi.uniqueUpToIso isInitialBot).hom := hi.hom_ext _ _
    rw [he]
    infer_instance

abbrev fullUnion : (simplex.{u} (bridge k n)).Subcomplex :=
  JTSubcomplexRangeUnion.union (prism c h n) (sideUnion c h n)

theorem fullUnion_weak : WeakEquivalence (fullUnion.{u} c h n).ι := by
  haveI := prism_weak.{u} c h n
  exact JTSubcomplexRangeUnion.union_weak _ _ (sideUnion_fromPreimage_weak c h n)

end

end DaggerModels.PartII.JTChangingCoefficientBridgeOverlap
