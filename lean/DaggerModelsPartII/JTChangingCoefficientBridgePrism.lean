import DaggerModelsPartII.JTChangingCoefficientBridgeOrder
import DaggerModelsPartII.JTChangingCoefficientBridgeTime
import DaggerModelsPartII.JTCommonCoefficientPrism
import DaggerModelsPartII.JTSubcomplexRangeUnion
import DaggerModelsPartII.JTFiniteSubcomplexPreimageGluing

/-!
# The actual union of the two side simplexes and the full joining prism
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial
open MonoidalCategory CartesianMonoidalCategory
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.JTChangingCoefficientBridgePrism

open JTChangingCoefficientBridgeOrder
open JTChangingCoefficientBridgeTime
open JTHigherInterleavedParameter (common)
open SSet.Subcomplex

noncomputable section

private abbrev simplex (k : SimplexCategory) := SSet.stdSimplex.{u}.obj k

variable {k b b' : SimplexCategory} (c : k ⟶ b) (h : b ⟶ b') (n : SimplexCategory)

/-- Interpret the joining time simplex as a copy and an original time. -/
def rankVertex (x : Fin (k.len + 1) × Fin ((time n).len + 1)) :
    Fin ((bridge k n).len + 1) :=
  let p := (timeVertexEquiv n).symm x.2
  vertexEquiv c h n ((x.1, p.2), p.1)

theorem rankVertex_apply (a : Fin (k.len + 1)) (e : Fin 2) (t : Fin (n.len + 1)) :
    rankVertex c h n (a, timeVertexEquiv n (e, t)) = vertexEquiv c h n ((a, t), e) := by
  unfold rankVertex
  rw [Equiv.symm_apply_apply]

theorem rankVertex_injective : Function.Injective (rankVertex c h n) := by
  intro x y he
  have h' := (vertexEquiv c h n).injective he
  apply Prod.ext
  · exact congrArg (fun z ↦ z.1.1) h'
  · apply (timeVertexEquiv n).symm.injective
    exact Prod.ext (congrArg Prod.snd h') (congrArg (fun z ↦ z.1.2) h')

theorem rankVertex_mono : Monotone (rankVertex c h n) := by
  rintro ⟨a, t⟩ ⟨a', t'⟩ hp
  obtain ⟨⟨e, t⟩, rfl⟩ := (timeVertexEquiv n).surjective t
  obtain ⟨⟨e', t'⟩, rfl⟩ := (timeVertexEquiv n).surjective t'
  rw [rankVertex_apply, rankVertex_apply]
  have he := le_copy n hp.2
  rcases lt_or_eq_of_le he with he | he
  · exact cross_copy_le c h n hp.1 t t' he
  · have ht := le_time_of_copy_eq n he hp.2
    exact (prismOrder c h n).monotone ⟨⟨hp.1, ht⟩, he.le⟩

/-- The full ordinary product with the joining time simplex. -/
def prism : simplex k ⊗ simplex (time n) ⟶ simplex (bridge k n) := by
  cases k using SimplexCategory.rec with
  | _ k =>
    cases n using SimplexCategory.rec with
    | _ n =>
      exact SSet.prodStdSimplex.homEquiv.symm
        (⟨rankVertex c h ⦋n⦌, rankVertex_mono c h ⦋n⦌⟩)

/-- The whole joining time simplex at one coefficient vertex. -/
def vertical (a : Fin (k.len + 1)) : time n ⟶ bridge k n :=
  SimplexCategory.Hom.mk ⟨fun v ↦ rankVertex c h n (a, v),
    fun _ _ hv ↦ rankVertex_mono c h n ⟨le_rfl, hv⟩⟩

/-- The full coefficient simplex at a given joining time vertex. -/
def slice (v : Fin ((time n).len + 1)) : k ⟶ bridge k n :=
  SimplexCategory.Hom.mk ⟨fun a ↦ rankVertex c h n (a, v),
    fun _ _ ha ↦ rankVertex_mono c h n ⟨ha, le_rfl⟩⟩

theorem slice_base (v : Fin ((time n).len + 1)) :
    slice c h n v ≫ base c h n = c ≫ h := by
  obtain ⟨⟨e, t⟩, rfl⟩ := (timeVertexEquiv n).surjective v
  ext a : 3
  change (base c h n).toOrderHom (rankVertex c h n (a, timeVertexEquiv n (e, t))) = _
  rw [rankVertex_apply, base_vertexEquiv]

theorem prism_app (q : SimplexCategoryᵒᵖ)
    (x : (simplex.{u} k ⊗ simplex (time n)).obj q) (a : Fin (q.unop.len + 1)) :
    (SSet.stdSimplex.objEquiv ((prism c h n).app q x)).toOrderHom a =
      rankVertex c h n ((SSet.stdSimplex.objEquiv x.1).toOrderHom a,
        (SSet.stdSimplex.objEquiv x.2).toOrderHom a) := by
  cases k using SimplexCategory.rec with
  | _ k =>
    cases n using SimplexCategory.rec with
    | _ n =>
      cases q using Opposite.rec with
      | op q =>
        cases q using SimplexCategory.rec with
        | h d => rfl

theorem verticalSection_prism (a : Fin (k.len + 1)) :
    JTHigherInterleavedParameter.verticalSection.{u} k (time n) a ≫ prism c h n =
      SSet.stdSimplex.map (vertical c h n a) := by
  apply NatTrans.ext
  funext q z
  apply SSet.stdSimplex.objEquiv.injective
  ext v : 3
  change (SSet.stdSimplex.objEquiv ((prism c h n).app q
    ((JTHigherInterleavedParameter.verticalSection.{u} k (time n) a).app q z))).toOrderHom v = _
  rw [prism_app]
  rfl

instance prism_mono : Mono (prism.{u} c h n) := by
  rw [NatTrans.mono_iff_mono_app]
  intro q
  apply (mono_iff_injective _).mpr
  intro x y hxy
  have H (a : Fin (q.unop.len + 1)) :
      ((SSet.stdSimplex.objEquiv x.1).toOrderHom a, (SSet.stdSimplex.objEquiv x.2).toOrderHom a) =
      ((SSet.stdSimplex.objEquiv y.1).toOrderHom a, (SSet.stdSimplex.objEquiv y.2).toOrderHom a) := by
    apply rankVertex_injective c h n
    rw [← prism_app, ← prism_app, hxy]
  apply Prod.ext
  · apply SSet.stdSimplex.objEquiv.injective
    ext a : 3
    exact congrArg Prod.fst (H a)
  · apply SSet.stdSimplex.objEquiv.injective
    ext a : 3
    exact congrArg Prod.snd (H a)

theorem prism_base :
    prism.{u} c h n ≫ SSet.stdSimplex.map (base c h n) =
      fst (simplex k) (simplex (time n)) ≫ SSet.stdSimplex.map (c ≫ h) := by
  apply NatTrans.ext
  funext q x
  apply SSet.stdSimplex.objEquiv.injective
  ext a : 3
  change (base c h n).toOrderHom
      ((SSet.stdSimplex.objEquiv ((prism c h n).app q x)).toOrderHom a) = _
  rw [prism_app]
  obtain ⟨⟨e, t⟩, ht⟩ := (timeVertexEquiv n).surjective
    ((SSet.stdSimplex.objEquiv x.2).toOrderHom a)
  rw [← ht, rankVertex_apply, base_vertexEquiv]
  rfl

/-- The full joining prism is a Kan trivial cofibration. -/
theorem prism_weak : WeakEquivalence (prism.{u} c h n) := by
  haveI := JTInterleavedParameter.standardMap_weak.{u} (base c h n)
  have h₀ := JTInterleavedParameter.standardMap_weak.{u} (c ≫ h)
  haveI : WeakEquivalence (snd (simplex.{u} (time n)) (simplex.{u} k)) := by
    let a := time n
    change WeakEquivalence (snd (simplex.{u} a) (simplex.{u} k))
    cases a using SimplexCategory.rec with
    | _ a => exact DaggerNativeContractibleSimplexParameter.simplexProjection_weakEquivalence a _
  have h₁ : WeakEquivalence (fst (simplex.{u} k) (simplex.{u} (time n))) := by
    rw [← braiding_hom_snd]
    infer_instance
  haveI : WeakEquivalence
      (fst (simplex.{u} k) (simplex.{u} (time n)) ≫ SSet.stdSimplex.map (c ≫ h)) :=
    (weakEquivalence_iff _).mpr ((weakEquivalences SSet.{u}).comp_mem _ _
      ((weakEquivalence_iff _).mp h₁) ((weakEquivalence_iff _).mp h₀))
  exact weakEquivalence_of_postcomp_of_fac (prism_base.{u} c h n)

/-- The existing common-coefficient prism on each of the two sides. -/
def sidePrism (e : Fin 2) : simplex k ⊗ simplex n ⟶ simplex (common k n) :=
  if e = 0 then JTCommonCoefficientParameter.prism c n
  else JTCommonCoefficientParameter.prism (c ≫ h) n

instance sidePrism_mono (e : Fin 2) : Mono (sidePrism.{u} c h n e) := by
  fin_cases e <;> simp [sidePrism] <;> infer_instance

theorem sidePrism_weak (e : Fin 2) : WeakEquivalence (sidePrism.{u} c h n e) := by
  fin_cases e
  · simpa only [sidePrism, if_pos rfl] using JTCommonCoefficientParameter.prism_weak.{u} c n
  · simpa only [sidePrism, if_neg (by decide : (1 : Fin 2) ≠ 0)] using
      JTCommonCoefficientParameter.prism_weak.{u} (c ≫ h) n

/-- The overlap with each old enlargement is the actual original
prism at that time face. -/
theorem prism_side (e : Fin 2) :
    (simplex.{u} k ◁ SSet.stdSimplex.map (timeSide n e)) ≫ prism c h n =
      sidePrism c h n e ≫ SSet.stdSimplex.map (side c h n e) := by
  cases k using SimplexCategory.rec with
  | _ k =>
    cases n using SimplexCategory.rec with
    | _ n =>
      apply NatTrans.ext
      funext q x
      cases q using Opposite.rec with
      | op q =>
        cases q using SimplexCategory.rec with
        | h d =>
          apply SSet.stdSimplex.objEquiv.injective
          ext a : 3
          fin_cases e
          · change (SSet.stdSimplex.objEquiv ((prism c h ⦋n⦌).app _
                (x.1, (SSet.stdSimplex.map (timeSide ⦋n⦌ 0)).app _ x.2))).toOrderHom a = _
            rw [prism_app]
            change rankVertex c h ⦋n⦌
              ((SSet.stdSimplex.objEquiv x.1).toOrderHom a,
                timeVertexEquiv ⦋n⦌ (0, (SSet.stdSimplex.objEquiv x.2).toOrderHom a)) =
              (side c h ⦋n⦌ 0).toOrderHom
                ((SSet.stdSimplex.objEquiv ((sidePrism c h ⦋n⦌ 0).app _ x)).toOrderHom a)
            rw [rankVertex_apply, sidePrism, if_pos rfl, JTCommonCoefficientParameter.prism_apply,
              side_vertexEquiv_zero]
            rfl
          · change (SSet.stdSimplex.objEquiv ((prism c h ⦋n⦌).app _
                (x.1, (SSet.stdSimplex.map (timeSide ⦋n⦌ 1)).app _ x.2))).toOrderHom a = _
            rw [prism_app]
            change rankVertex c h ⦋n⦌
              ((SSet.stdSimplex.objEquiv x.1).toOrderHom a,
                timeVertexEquiv ⦋n⦌ (1, (SSet.stdSimplex.objEquiv x.2).toOrderHom a)) =
              (side c h ⦋n⦌ 1).toOrderHom
                ((SSet.stdSimplex.objEquiv ((sidePrism c h ⦋n⦌ 1).app _ x)).toOrderHom a)
            rw [rankVertex_apply, sidePrism, if_neg (by decide : (1 : Fin 2) ≠ 0),
              JTCommonCoefficientParameter.prism_apply, side_vertexEquiv_one]
            rfl

end

end DaggerModels.PartII.JTChangingCoefficientBridgePrism
