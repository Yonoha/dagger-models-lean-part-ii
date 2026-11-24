import DaggerModelsPartII.JTInterleavedParameter
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Interleaving in arbitrary finite time degree

A vertex of the common simplex represents a pair consisting of an original
vertex and a time vertex, ordered first by the original coordinate.
-/

set_option autoImplicit false

open CategoryTheory Simplicial MonoidalCategory CartesianMonoidalCategory
open HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.JTHigherInterleavedParameter

noncomputable section

/-- The ordered simplex on the lexicographically enumerated pairs. -/
def common (k n : SimplexCategory) : SimplexCategory := ⦋k.len * (n.len + 1) + n.len⦌

private theorem card (k n : SimplexCategory) :
    (common k n).len + 1 = (k.len + 1) * (n.len + 1) := by
  change k.len * (n.len + 1) + n.len + 1 = _
  rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc]

/-- The common simplex retains exactly one vertex for each pair. -/
def vertexEquiv (k n : SimplexCategory) :
    Fin (k.len + 1) × Fin (n.len + 1) ≃ Fin ((common k n).len + 1) :=
  finProdFinEquiv.trans (finCongr (card k n).symm)

@[simp] theorem vertexEquiv_val (k n : SimplexCategory)
    (x : Fin (k.len + 1) × Fin (n.len + 1)) :
    (vertexEquiv k n x).val = x.2.val + (n.len + 1) * x.1.val := rfl

private theorem vertexEquiv_mono (k n : SimplexCategory) :
    Monotone (vertexEquiv k n) := by
  intro x y h
  change (vertexEquiv k n x).val ≤ (vertexEquiv k n y).val
  simp only [vertexEquiv_val]
  exact Nat.add_le_add h.2 (Nat.mul_le_mul_left _ h.1)

/-- The inclusion of the coordinatewise ordered product. -/
def prismOrder (k n : SimplexCategory) :
    Fin (k.len + 1) × Fin (n.len + 1) →o Fin ((common k n).len + 1) :=
  ⟨vertexEquiv k n, vertexEquiv_mono k n⟩

/-- The full time slice of the common simplex. -/
def slice (k n : SimplexCategory) (t : Fin (n.len + 1)) : k ⟶ common k n :=
  SimplexCategory.Hom.mk ⟨fun a ↦ vertexEquiv k n (a, t),
    fun _ _ h ↦ vertexEquiv_mono k n ⟨h, le_rfl⟩⟩

/-- The full time simplex at an original vertex. -/
def vertical (k n : SimplexCategory) (a : Fin (k.len + 1)) : n ⟶ common k n :=
  SimplexCategory.Hom.mk ⟨fun t ↦ vertexEquiv k n (a, t),
    fun _ _ h ↦ vertexEquiv_mono k n ⟨le_rfl, h⟩⟩

/-- Forget the time coordinate of a common vertex. -/
def ret (k n : SimplexCategory) : common k n ⟶ k :=
  SimplexCategory.Hom.mk
    ⟨fun x ↦ ((vertexEquiv k n).symm x).1, by
      intro x y h
      change x.val / (n.len + 1) ≤ y.val / (n.len + 1)
      exact Nat.div_le_div_right h⟩

@[simp] theorem ret_vertexEquiv (k n : SimplexCategory)
    (x : Fin (k.len + 1) × Fin (n.len + 1)) :
    (ret k n).toOrderHom (vertexEquiv k n x) = x.1 :=
  congrArg Prod.fst ((vertexEquiv k n).symm_apply_apply x)

theorem slice_ret (k n : SimplexCategory) (t : Fin (n.len + 1)) :
    slice k n t ≫ ret k n = 𝟙 k := by
  ext a : 3
  exact ret_vertexEquiv k n (a, t)

theorem vertical_ret (k n : SimplexCategory) (a : Fin (k.len + 1)) :
    vertical k n a ≫ ret k n = SimplexCategory.const n k a := by
  ext t : 3
  exact ret_vertexEquiv k n (a, t)

/-- The product of standard simplices inside the common simplex. -/
def prism (k n : SimplexCategory) :
    (SSet.stdSimplex.obj k : SSet.{u}) ⊗ SSet.stdSimplex.obj n ⟶
      SSet.stdSimplex.obj (common k n) := by
  induction k using SimplexCategory.rec with
  | _ k =>
    induction n using SimplexCategory.rec with
    | _ n => exact SSet.prodStdSimplex.homEquiv.symm (prismOrder ⦋k⦌ ⦋n⦌)

private theorem prism_apply (k n d : ℕ)
    (x : ((Δ[k] : SSet.{u}) ⊗ Δ[n]).obj (Opposite.op ⦋d⦌))
    (a : Fin (d + 1)) :
    (SSet.stdSimplex.objEquiv ((prism ⦋k⦌ ⦋n⦌).app (Opposite.op ⦋d⦌) x)).toOrderHom a =
      vertexEquiv ⦋k⦌ ⦋n⦌ (SSet.prodStdSimplex.objEquiv x a) := rfl

instance prism_mono (k n : SimplexCategory) : Mono (prism.{u} k n) := by
  induction k using SimplexCategory.rec with
  | _ k =>
    induction n using SimplexCategory.rec with
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
          apply (vertexEquiv ⦋k⦌ ⦋n⦌).injective
          have h := congrArg (fun z ↦
            (SSet.stdSimplex.objEquiv z).toOrderHom a) hxy
          simpa only [prism_apply] using h

theorem prism_ret (k n : SimplexCategory) :
    prism.{u} k n ≫ SSet.stdSimplex.map (ret k n) =
      fst (SSet.stdSimplex.obj k : SSet.{u}) (SSet.stdSimplex.obj n) := by
  induction k using SimplexCategory.rec with
  | _ k =>
    induction n using SimplexCategory.rec with
    | _ n =>
      apply NatTrans.ext
      funext q x
      induction q using Opposite.rec with | op q =>
        induction q using SimplexCategory.rec with | h d =>
          apply SSet.stdSimplex.objEquiv.injective
          ext a : 3
          exact ret_vertexEquiv ⦋k⦌ ⦋n⦌ (SSet.prodStdSimplex.objEquiv x a)

theorem prism_weak (k n : SimplexCategory) : WeakEquivalence (prism.{u} k n) := by
  haveI := JTInterleavedParameter.standardMap_weak.{u} (ret k n)
  haveI : WeakEquivalence (snd (SSet.stdSimplex.obj n : SSet.{u})
      (SSet.stdSimplex.obj k : SSet.{u})) := by
    induction n using SimplexCategory.rec with
    | _ n => exact DaggerNativeContractibleSimplexParameter.simplexProjection_weakEquivalence n _
  haveI : WeakEquivalence (fst (SSet.stdSimplex.obj k : SSet.{u})
      (SSet.stdSimplex.obj n : SSet.{u})) := by
    rw [← braiding_hom_snd]
    infer_instance
  exact weakEquivalence_of_postcomp_of_fac (prism_ret.{u} k n)

/-- The Cartesian inclusion of a whole time slice. -/
def ordinarySlice (k n : SimplexCategory) (t : Fin (n.len + 1)) :
    (SSet.stdSimplex.obj k : SSet.{u}) ⟶
      (SSet.stdSimplex.obj k : SSet.{u}) ⊗ SSet.stdSimplex.obj n :=
  lift (𝟙 (SSet.stdSimplex.obj k : SSet.{u}))
    (SSet.stdSimplex.map (SimplexCategory.const k n t))

theorem ordinarySlice_prism (k n : SimplexCategory) (t : Fin (n.len + 1)) :
    ordinarySlice.{u} k n t ≫ prism k n = SSet.stdSimplex.map (slice k n t) := by
  induction k using SimplexCategory.rec with
  | _ k =>
    induction n using SimplexCategory.rec with
    | _ n => rfl

/-- The Cartesian inclusion of the time simplex at a chosen original vertex. -/
def verticalSection (k n : SimplexCategory) (a : Fin (k.len + 1)) :
    (SSet.stdSimplex.obj n : SSet.{u}) ⟶
      (SSet.stdSimplex.obj k : SSet.{u}) ⊗ SSet.stdSimplex.obj n :=
  lift (SSet.stdSimplex.map (SimplexCategory.const n k a))
    (𝟙 (SSet.stdSimplex.obj n : SSet.{u}))

theorem verticalSection_prism (k n : SimplexCategory) (a : Fin (k.len + 1)) :
    verticalSection.{u} k n a ≫ prism k n = SSet.stdSimplex.map (vertical k n a) := by
  induction k using SimplexCategory.rec with
  | _ k =>
    induction n using SimplexCategory.rec with
    | _ n => rfl

end

end DaggerModels.PartII.JTHigherInterleavedParameter
