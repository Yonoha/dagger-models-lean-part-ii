import DaggerModelsPartII.JTFiniteCoefficientBridgeOrder
import DaggerModelsPartII.JTFiniteCoefficientBridgeTime
import DaggerModelsPartII.JTCommonCoefficientPrism

/-!
# The full ordinary prism through a finite family of coefficient orders
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial
open MonoidalCategory CartesianMonoidalCategory
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.JTFiniteCoefficientBridgePrism

open JTFiniteCoefficientBridgeOrder
open JTFiniteCoefficientBridgeTime
open JTHigherInterleavedParameter (common)
open SSet.Subcomplex

noncomputable section

private abbrev simplex (k : SimplexCategory) := SSet.stdSimplex.{u}.obj k

variable {m : ℕ} {k b' : SimplexCategory} {b : Fin (m + 1) → SimplexCategory}
variable (c : ∀ e, k ⟶ b e) (u : k ⟶ b') (n : SimplexCategory)

/-- Interpret the joining time simplex as a copy and an original time. -/
def rankVertex (x : Fin (k.len + 1) × Fin ((time m n).len + 1)) :
    Fin ((bridge k n m).len + 1) :=
  let p := (timeVertexEquiv m n).symm x.2
  vertexEquiv c u n ((x.1, p.2), p.1)

theorem rankVertex_apply (a : Fin (k.len + 1)) (e : Fin (m + 1)) (t : Fin (n.len + 1)) :
    rankVertex c u n (a, timeVertexEquiv m n (e, t)) = vertexEquiv c u n ((a, t), e) := by
  unfold rankVertex
  rw [Equiv.symm_apply_apply]

theorem rankVertex_injective : Function.Injective (rankVertex c u n) := by
  intro x y he
  have h' := (vertexEquiv c u n).injective he
  apply Prod.ext
  · exact congrArg (fun z ↦ z.1.1) h'
  · apply (timeVertexEquiv m n).symm.injective
    exact Prod.ext (congrArg Prod.snd h') (congrArg (fun z ↦ z.1.2) h')

theorem rankVertex_mono : Monotone (rankVertex c u n) := by
  rintro ⟨a, t⟩ ⟨a', t'⟩ hp
  obtain ⟨⟨e, t⟩, rfl⟩ := (timeVertexEquiv m n).surjective t
  obtain ⟨⟨e', t'⟩, rfl⟩ := (timeVertexEquiv m n).surjective t'
  rw [rankVertex_apply, rankVertex_apply]
  have he := le_copy m n hp.2
  rcases lt_or_eq_of_le he with he | he
  · exact cross_copy_le c u n hp.1 t t' he
  · have ht := le_time_of_copy_eq m n he hp.2
    change e = e' at he
    subst e'
    exact same_copy_le c u n e hp.1 ht

/-- The full ordinary product with the joining time simplex. -/
def prism : simplex k ⊗ simplex (time m n) ⟶ simplex (bridge k n m) := by
  cases k using SimplexCategory.rec with
  | _ k =>
    cases n using SimplexCategory.rec with
    | _ n =>
      exact SSet.prodStdSimplex.homEquiv.symm
        (⟨rankVertex c u ⦋n⦌, rankVertex_mono c u ⦋n⦌⟩)

/-- The whole joining time simplex at one coefficient vertex. -/
def vertical (a : Fin (k.len + 1)) : time m n ⟶ bridge k n m :=
  SimplexCategory.Hom.mk ⟨fun v ↦ rankVertex c u n (a, v),
    fun _ _ hv ↦ rankVertex_mono c u n ⟨le_rfl, hv⟩⟩

/-- The full coefficient simplex at a given joining time vertex. -/
def slice (v : Fin ((time m n).len + 1)) : k ⟶ bridge k n m :=
  SimplexCategory.Hom.mk ⟨fun a ↦ rankVertex c u n (a, v),
    fun _ _ ha ↦ rankVertex_mono c u n ⟨ha, le_rfl⟩⟩

theorem slice_base (v : Fin ((time m n).len + 1)) :
    slice c u n v ≫ base c u n = u := by
  obtain ⟨⟨e, t⟩, rfl⟩ := (timeVertexEquiv m n).surjective v
  ext a : 3
  change (base c u n).toOrderHom (rankVertex c u n (a, timeVertexEquiv m n (e, t))) = _
  rw [rankVertex_apply, base_vertexEquiv]

theorem prism_app (q : SimplexCategoryᵒᵖ)
    (x : (simplex.{u} k ⊗ simplex (time m n)).obj q) (a : Fin (q.unop.len + 1)) :
    (SSet.stdSimplex.objEquiv ((prism c u n).app q x)).toOrderHom a =
      rankVertex c u n ((SSet.stdSimplex.objEquiv x.1).toOrderHom a,
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
    JTHigherInterleavedParameter.verticalSection.{u} k (time m n) a ≫ prism c u n =
      SSet.stdSimplex.map (vertical c u n a) := by
  apply NatTrans.ext
  funext q z
  apply SSet.stdSimplex.objEquiv.injective
  ext v : 3
  change (SSet.stdSimplex.objEquiv ((prism c u n).app q
    ((JTHigherInterleavedParameter.verticalSection.{u} k (time m n) a).app q z))).toOrderHom v = _
  rw [prism_app]
  rfl

instance prism_mono : Mono (prism.{u} c u n) := by
  rw [NatTrans.mono_iff_mono_app]
  intro q
  apply (mono_iff_injective _).mpr
  intro x y hxy
  have H (a : Fin (q.unop.len + 1)) :
      ((SSet.stdSimplex.objEquiv x.1).toOrderHom a, (SSet.stdSimplex.objEquiv x.2).toOrderHom a) =
      ((SSet.stdSimplex.objEquiv y.1).toOrderHom a, (SSet.stdSimplex.objEquiv y.2).toOrderHom a) := by
    apply rankVertex_injective c u n
    rw [← prism_app, ← prism_app, hxy]
  apply Prod.ext
  · apply SSet.stdSimplex.objEquiv.injective
    ext a : 3
    exact congrArg Prod.fst (H a)
  · apply SSet.stdSimplex.objEquiv.injective
    ext a : 3
    exact congrArg Prod.snd (H a)

theorem prism_base :
    prism.{u} c u n ≫ SSet.stdSimplex.map (base c u n) =
      fst (simplex k) (simplex (time m n)) ≫ SSet.stdSimplex.map u := by
  apply NatTrans.ext
  funext q x
  apply SSet.stdSimplex.objEquiv.injective
  ext a : 3
  change (base c u n).toOrderHom
      ((SSet.stdSimplex.objEquiv ((prism c u n).app q x)).toOrderHom a) = _
  rw [prism_app]
  obtain ⟨⟨e, t⟩, ht⟩ := (timeVertexEquiv m n).surjective
    ((SSet.stdSimplex.objEquiv x.2).toOrderHom a)
  rw [← ht, rankVertex_apply, base_vertexEquiv]
  rfl

/-- The full joining prism is a Kan trivial cofibration. -/
theorem prism_weak : WeakEquivalence (prism.{u} c u n) := by
  haveI := JTInterleavedParameter.standardMap_weak.{u} (base c u n)
  have h₀ := JTInterleavedParameter.standardMap_weak.{u} u
  haveI : WeakEquivalence (snd (simplex.{u} (time m n)) (simplex.{u} k)) := by
    let a := time m n
    change WeakEquivalence (snd (simplex.{u} a) (simplex.{u} k))
    cases a using SimplexCategory.rec with
    | _ a => exact DaggerNativeContractibleSimplexParameter.simplexProjection_weakEquivalence a _
  have h₁ : WeakEquivalence (fst (simplex.{u} k) (simplex.{u} (time m n))) := by
    rw [← braiding_hom_snd]
    infer_instance
  haveI : WeakEquivalence
      (fst (simplex.{u} k) (simplex.{u} (time m n)) ≫ SSet.stdSimplex.map u) :=
    (weakEquivalence_iff _).mpr ((weakEquivalences SSet.{u}).comp_mem _ _
      ((weakEquivalence_iff _).mp h₁) ((weakEquivalence_iff _).mp h₀))
  exact weakEquivalence_of_postcomp_of_fac (prism_base.{u} c u n)

variable (h : ∀ e, b e ⟶ b') (hu : ∀ e, c e ≫ h e = u)

/-- The old prism is the restriction of the full joining prism at its time face. -/
theorem prism_side (e : Fin (m + 1)) :
    (simplex.{u} k ◁ SSet.stdSimplex.map (timeSide n e)) ≫ prism c u n =
      JTCommonCoefficientParameter.prism (c e) n ≫ SSet.stdSimplex.map (side c u h hu n e) := by
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
          change (SSet.stdSimplex.objEquiv ((prism c u ⦋n⦌).app _
            (x.1, (SSet.stdSimplex.map (timeSide ⦋n⦌ e)).app _ x.2))).toOrderHom a = _
          rw [prism_app]
          change rankVertex c u ⦋n⦌
            ((SSet.stdSimplex.objEquiv x.1).toOrderHom a,
              timeVertexEquiv m ⦋n⦌ (e, (SSet.stdSimplex.objEquiv x.2).toOrderHom a)) =
            (side c u h hu ⦋n⦌ e).toOrderHom
              ((SSet.stdSimplex.objEquiv
                ((JTCommonCoefficientParameter.prism (c e) ⦋n⦌).app _ x)).toOrderHom a)
          rw [rankVertex_apply, JTCommonCoefficientParameter.prism_apply, side_vertexEquiv]
          rfl

end

end DaggerModels.PartII.JTFiniteCoefficientBridgePrism
