import DaggerModelsPartII.JTInterleavedParameter
import DaggerModelsPartII.JTRelativeEndpointPrism

/-!
# Extend the two relative faces to one ordered parameter
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra
open CartesianMonoidalCategory
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTEndpointPrismExtension

open JTInterleavedParameter

noncomputable section

private abbrev Δ (k : SimplexCategory) := SSet.stdSimplex.{0}.obj k
private abbrev I := Δ ⦋1⦌
private abbrev A := Δ ⦋0⦌
private abbrev vertex (k : SimplexCategory) (a : Fin (k.len + 1)) :=
  SSet.stdSimplex.{0}.map (SimplexCategory.const ⦋0⦌ k a)
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

private theorem ordinarySlice_eq (k : SimplexCategory) (t : Fin 2) :
    JTRelativeEndpointPrism.timeSlice (Δ k) t = ordinarySlice k t := by
  have hδ : (if t = 0 then SSet.boundary₁.ι₀ else SSet.boundary₁.ι₁) ≫
      (SSet.boundary.{0} 1).ι = vertex ⦋1⦌ t := by
    fin_cases t
    · change SSet.boundary₁.ι₀ ≫ (SSet.boundary.{0} 1).ι = _
      rw [SSet.boundary₁.ι₀_ι, SSet.stdSimplex.δ_one]
      rfl
    · change SSet.boundary₁.ι₁ ≫ (SSet.boundary.{0} 1).ι = _
      rw [SSet.boundary₁.ι₁_ι, SSet.stdSimplex.δ_zero]
      rfl
  unfold JTRelativeEndpointPrism.timeSlice ordinarySlice
  rw [← MonoidalCategory.whiskerLeft_comp, hδ]
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, whiskerLeft_fst, SSet.stdSimplex.rightUnitor_inv_fst, lift_fst]
  · rw [Category.assoc, whiskerLeft_snd, lift_snd, ← Category.assoc]
    have h : (SSet.stdSimplex.rightUnitor (Δ k)).inv ≫ snd (Δ k) A =
        SSet.stdSimplex.map (SimplexCategory.const k ⦋0⦌ 0) :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [h, ← SSet.stdSimplex.{0}.map_comp, SimplexCategory.const_comp]
    rfl

private theorem verticalSection_eq (k : SimplexCategory) (a : Fin (k.len + 1)) :
    lift (term I) (𝟙 I) ≫ (vertex k a ⊗ₘ 𝟙 I) = verticalSection k a := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, tensorHom_fst, lift_fst_assoc, verticalSection, lift_fst]
    have h : term I = SSet.stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0) :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [h, ← SSet.stdSimplex.{0}.map_comp, SimplexCategory.const_comp]
    rfl
  · simp only [verticalSection, Category.assoc, tensorHom_snd, lift_snd, Category.comp_id]

/-- Both original faces extend to a single standard-simplex coefficient,
with the entire duplicate edge fixed and the base pulled back by the
interleaved retraction. -/
theorem exists_extension (k : SimplexCategory) (a : Fin (k.len + 1))
    {X Y : SSet.{0}} (p : X ⟶ Y) [Fibration p]
    (b : Δ k ⟶ Y) (t : A ⟶ X)
    (e₀ e₁ : Δ k ⟶ X)
    (hb₀ : e₀ ≫ p = b) (hb₁ : e₁ ≫ p = b)
    (ht₀ : vertex k a ≫ e₀ = t) (ht₁ : vertex k a ≫ e₁ = t) :
    ∃ E : Δ (common k) ⟶ X,
      SSet.stdSimplex.map (slice k 0) ≫ E = e₀ ∧
      SSet.stdSimplex.map (slice k 1) ≫ E = e₁ ∧
      SSet.stdSimplex.map (edge k a) ≫ E = term I ≫ t ∧
      E ≫ p = SSet.stdSimplex.map (ret k) ≫ b := by
  haveI : Mono (vertex k a) := SSet.stdSimplex.isTerminalObj₀.mono_from _
  haveI : WeakEquivalence (vertex k a) := standardMap_weak _
  obtain ⟨F, h₀, h₁, ha, hF⟩ :=
    JTRelativeEndpointPrism.exists_relativePrism (vertex k a) p b t e₀ e₁
      hb₀ hb₁ ht₀ ht₁
  haveI : Cofibration (prism.{0} k) :=
    (SSet.modelCategoryQuillen.cofibration_iff _).mpr inferInstance
  haveI := prism_weak.{0} k
  let sq : CommSq F (prism k) p (SSet.stdSimplex.map (ret k) ≫ b) := by
    constructor
    rw [hF, ← Category.assoc, prism_ret]
  refine ⟨sq.lift, ?_, ?_, ?_, sq.fac_right⟩
  · rw [← ordinarySlice_prism, Category.assoc, sq.fac_left, ← ordinarySlice_eq]
    exact h₀
  · rw [← ordinarySlice_prism, Category.assoc, sq.fac_left, ← ordinarySlice_eq]
    exact h₁
  · rw [← verticalSection_prism, Category.assoc, sq.fac_left,
      ← verticalSection_eq, Category.assoc, ha, ← Category.assoc, lift_fst]

end

end DaggerModels.PartII.JTEndpointPrismExtension
