import DaggerModelsPartII.JTCommonCoefficientParameter
import TopCatModelCategory.SemiSimplexCategory
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# The full simplicial prism over a common coefficient
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.JTCommonCoefficientParameter

open JTHigherInterleavedParameter (common)

noncomputable section

variable {k l b n m : SimplexCategory}

private abbrev simplex (k : SimplexCategory) := SSet.stdSimplex.{u}.obj k

/-- The ordinary product prism is included in the actual ordered
standard simplex over the common coefficient. -/
def prism (c : k ⟶ b) (n : SimplexCategory) :
    simplex k ⊗ simplex n ⟶ simplex (common k n) := by
  cases k using SimplexCategory.rec with
  | _ k =>
    cases n using SimplexCategory.rec with
    | _ n => exact SSet.prodStdSimplex.homEquiv.symm (prismOrder c ⦋n⦌)

theorem prism_apply (k n d : ℕ) (c : ⦋k⦌ ⟶ b)
    (x : (simplex ⦋k⦌ ⊗ simplex ⦋n⦌).obj (op ⦋d⦌))
    (a : Fin (d + 1)) :
    (SSet.stdSimplex.objEquiv ((prism c ⦋n⦌).app (op ⦋d⦌) x)).toOrderHom a =
      vertexEquiv c ⦋n⦌ (SSet.prodStdSimplex.objEquiv x a) := rfl

instance prism_mono (c : k ⟶ b) (n : SimplexCategory) : Mono (prism.{u} c n) := by
  cases k using SimplexCategory.rec with
  | _ k =>
    cases n using SimplexCategory.rec with
    | _ n =>
      rw [NatTrans.mono_iff_mono_app]
      intro q
      induction q using Opposite.rec with | op q =>
        induction q using SimplexCategory.rec with | h d =>
          apply (mono_iff_injective _).mpr
          intro x y hxy
          apply SSet.prodStdSimplex.objEquiv.injective
          apply OrderHom.ext
          funext a
          apply (vertexEquiv c ⦋n⦌).injective
          have h := congrArg (fun z ↦ (SSet.stdSimplex.objEquiv z).toOrderHom a) hxy
          simpa only [prism_apply] using h

/-- The prism projects to the original source coefficient followed
by the given operator to the common coefficient. -/
theorem prism_base (c : k ⟶ b) (n : SimplexCategory) :
    prism.{u} c n ≫ SSet.stdSimplex.map (base c n) =
      fst (simplex k) (simplex n) ≫ SSet.stdSimplex.map c := by
  cases k using SimplexCategory.rec with
  | _ k =>
    cases n using SimplexCategory.rec with
    | _ n =>
      apply NatTrans.ext
      funext q x
      induction q using Opposite.rec with | op q =>
        induction q using SimplexCategory.rec with | h d =>
          apply SSet.stdSimplex.objEquiv.injective
          ext a : 3
          exact base_vertexEquiv c ⦋n⦌ (SSet.prodStdSimplex.objEquiv x a)

/-- This prism inclusion is still a Kan trivial cofibration. -/
theorem prism_weak (c : k ⟶ b) (n : SimplexCategory) : WeakEquivalence (prism.{u} c n) := by
  haveI := JTInterleavedParameter.standardMap_weak.{u} (base c n)
  have hc := JTInterleavedParameter.standardMap_weak.{u} c
  haveI : WeakEquivalence (snd (simplex.{u} n) (simplex.{u} k)) := by
    cases n using SimplexCategory.rec with
    | _ n => exact DaggerNativeContractibleSimplexParameter.simplexProjection_weakEquivalence n _
  have hfst : WeakEquivalence (fst (simplex.{u} k) (simplex.{u} n)) := by
    rw [← braiding_hom_snd]
    infer_instance
  haveI : WeakEquivalence (fst (simplex.{u} k) (simplex.{u} n) ≫ SSet.stdSimplex.map c) :=
    (weakEquivalence_iff _).mpr ((weakEquivalences SSet.{u}).comp_mem _ _
      ((weakEquivalence_iff _).mp hfst) ((weakEquivalence_iff _).mp hc))
  exact weakEquivalence_of_postcomp_of_fac (prism_base.{u} c n)

/-- The inclusion is natural in both the given coefficient operator
and the given injective time operator. -/
theorem prism_map {c : k ⟶ b} {d : l ⟶ b} (f : k ⟶ l) (hf : f ≫ d = c)
    (j : n ⟶ m) (hj : Function.Injective j.toOrderHom) :
    prism.{u} c n ≫ SSet.stdSimplex.map (map f hf j hj) =
      (SSet.stdSimplex.map f ⊗ₘ SSet.stdSimplex.map j) ≫ prism d m := by
  cases k using SimplexCategory.rec with
  | _ k =>
    cases l using SimplexCategory.rec with
    | _ l =>
      cases n using SimplexCategory.rec with
      | _ n =>
        cases m using SimplexCategory.rec with
        | _ m =>
          apply NatTrans.ext
          funext q x
          induction q using Opposite.rec with | op q =>
            induction q using SimplexCategory.rec with | h r =>
              apply SSet.stdSimplex.objEquiv.injective
              ext a : 3
              exact map_vertexEquiv f hf j hj (SSet.prodStdSimplex.objEquiv x a)

theorem ordinarySlice_prism (c : k ⟶ b) (n : SimplexCategory) (t : Fin (n.len + 1)) :
    JTHigherInterleavedParameter.ordinarySlice.{u} k n t ≫ prism c n =
      SSet.stdSimplex.map (slice c n t) := by
  cases k using SimplexCategory.rec with
  | _ k =>
    cases n using SimplexCategory.rec with
    | _ n => rfl

theorem verticalSection_prism (c : k ⟶ b) (n : SimplexCategory) (a : Fin (k.len + 1)) :
    JTHigherInterleavedParameter.verticalSection.{u} k n a ≫ prism c n =
      SSet.stdSimplex.map (vertical c n a) := by
  cases k using SimplexCategory.rec with
  | _ k =>
    cases n using SimplexCategory.rec with
    | _ n => rfl

open SemiSimplexCategory

private theorem mono_time {n m : SemiSimplexCategory} (j : n ⟶ m) :
    Function.Injective (toSimplexCategory.map j).toOrderHom :=
  SimplexCategory.mono_iff_injective.mp inferInstance

/-- The ordered parameter is a functor of arbitrary coefficient
operators over a fixed base and of time embeddings. -/
def parameter (b : SimplexCategory) : (Over b × SemiSimplexCategory) ⥤ SimplexCategory where
  obj z := common z.1.left (toSimplexCategory.obj z.2)
  map f := map f.1.left (Over.w f.1) (toSimplexCategory.map f.2) (mono_time f.2)
  map_id z := map_id z.1.hom (toSimplexCategory.obj z.2)
  map_comp f g := map_comp f.1.left g.1.left (Over.w f.1) (Over.w g.1)
    (toSimplexCategory.map f.2) (toSimplexCategory.map g.2) (mono_time f.2) (mono_time g.2)

end

end DaggerModels.PartII.JTCommonCoefficientParameter
