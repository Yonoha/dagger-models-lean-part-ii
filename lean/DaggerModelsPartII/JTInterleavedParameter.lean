import NativeCoherentCotensorResolutionWeak
import TopCatModelCategory.SSet.ProdSimplex
import Lean.Elab.Tactic.Omega

/-!
# The interleaved simplex parameter

The vertices of `common k` are ordered as
`(0,0), (0,1), (1,0), (1,1), ...`.  The two copies of `k` and the
vertical edges are retained as actual maps of standard simplices.
-/

set_option autoImplicit false

open CategoryTheory Simplicial MonoidalCategory CartesianMonoidalCategory
open HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.JTInterleavedParameter

noncomputable section

/-- One ordered simplex containing both parameter slices. -/
def common (k : SimplexCategory) : SimplexCategory := ⦋2 * k.len + 1⦌

/-- The copy of `k` at interval height `t`. -/
def slice (k : SimplexCategory) (t : Fin 2) : k ⟶ common k :=
  SimplexCategory.Hom.mk
    ⟨fun i ↦ ⟨2 * i.val + t.val, by
      have hi := i.isLt
      have ht : t.val < 2 := t.isLt
      change 2 * _ + _ < 2 * k.len + 1 + 1
      omega⟩, by
      intro i j hij
      change 2 * i.val + t.val ≤ 2 * j.val + t.val
      have hijv : i.val ≤ j.val := Fin.le_iff_val_le_val.mp hij
      omega⟩

@[simp] theorem slice_apply (k : SimplexCategory) (t : Fin 2)
    (i : Fin (k.len + 1)) :
    ((slice k t).toOrderHom i).val = 2 * i.val + t.val := rfl

/-- Forget the interval height of an interleaved vertex. -/
def ret (k : SimplexCategory) : common k ⟶ k :=
  SimplexCategory.Hom.mk
    ⟨fun i ↦ ⟨i.val / 2, by
      have hi := i.isLt
      change i.val < 2 * k.len + 1 + 1 at hi
      omega⟩, by
      intro i j hij
      change i.val / 2 ≤ j.val / 2
      have hijv : i.val ≤ j.val := Fin.le_iff_val_le_val.mp hij
      omega⟩

@[simp] theorem ret_apply (k : SimplexCategory)
    (i : Fin (2 * k.len + 2)) :
    ((ret k).toOrderHom i).val = i.val / 2 := rfl

/-- The edge joining the two copies of the vertex `a`. -/
def edge (k : SimplexCategory) (a : Fin (k.len + 1)) :
    ⦋1⦌ ⟶ common k :=
  SimplexCategory.Hom.mk
    ⟨fun t ↦ ⟨2 * a.val + t.val, by
      have ha := a.isLt
      have ht : t.val < 2 := t.isLt
      change 2 * _ + _ < 2 * k.len + 1 + 1
      omega⟩, by
      intro t s hts
      change 2 * a.val + t.val ≤ 2 * a.val + s.val
      have htsv : t.val ≤ s.val := Fin.le_iff_val_le_val.mp hts
      omega⟩

@[simp] theorem edge_apply (k : SimplexCategory)
    (a : Fin (k.len + 1)) (t : Fin 2) :
    ((edge k a).toOrderHom t).val = 2 * a.val + t.val := rfl

theorem slice_ret (k : SimplexCategory) (t : Fin 2) :
    slice k t ≫ ret k = 𝟙 k := by
  ext i : 3
  apply Fin.ext
  change (2 * i.val + t.val) / 2 = i.val
  have ht : t.val < 2 := t.isLt
  omega

theorem edge_ret (k : SimplexCategory) (a : Fin (k.len + 1)) :
    edge k a ≫ ret k = SimplexCategory.const ⦋1⦌ k a := by
  ext t : 3
  apply Fin.ext
  change (2 * a.val + t.val) / 2 = a.val
  have ht : t.val < 2 := t.isLt
  omega

theorem edge_endpoint (k : SimplexCategory)
    (a : Fin (k.len + 1)) (t : Fin 2) :
    SimplexCategory.const ⦋0⦌ ⦋1⦌ t ≫ edge k a =
      SimplexCategory.const ⦋0⦌ k a ≫ slice k t := by
  ext i : 3
  apply Fin.ext
  rfl

/-- The lexicographic embedding of the product poset. -/
def prismOrder (k : SimplexCategory) :
    Fin (k.len + 1) × Fin 2 →o Fin (2 * k.len + 2) where
  toFun x := ⟨2 * x.1.val + x.2.val, by
    have hx := x.1.isLt
    have ht := x.2.isLt
    omega⟩
  monotone' x y hxy := by
    change 2 * x.1.val + x.2.val ≤ 2 * y.1.val + y.2.val
    have h₁ : x.1.val ≤ y.1.val := Fin.le_iff_val_le_val.mp hxy.1
    have h₂ : x.2.val ≤ y.2.val := Fin.le_iff_val_le_val.mp hxy.2
    omega

theorem prismOrder_injective (k : SimplexCategory) :
    Function.Injective (prismOrder k) := by
  intro x y hxy
  apply Prod.ext
  · apply Fin.ext
    have h := congrArg Fin.val hxy
    change 2 * x.1.val + x.2.val = 2 * y.1.val + y.2.val at h
    have hx := x.2.isLt
    have hy := y.2.isLt
    omega
  · apply Fin.ext
    have h := congrArg Fin.val hxy
    change 2 * x.1.val + x.2.val = 2 * y.1.val + y.2.val at h
    have hx := x.2.isLt
    have hy := y.2.isLt
    omega

/-- The ordinary simplicial prism, embedded in the larger simplex. -/
def prism (k : SimplexCategory) :
    (SSet.stdSimplex.obj k : SSet.{u}) ⊗ Δ[1] ⟶ SSet.stdSimplex.obj (common k) := by
  induction k using SimplexCategory.rec with
  | _ n => exact SSet.prodStdSimplex.homEquiv.symm (prismOrder ⦋n⦌)

private theorem prism_apply (k n : ℕ)
    (x : ((Δ[k] : SSet.{u}) ⊗ Δ[1]).obj (Opposite.op ⦋n⦌))
    (i : Fin (n + 1)) :
    (SSet.stdSimplex.objEquiv ((prism ⦋k⦌).app (Opposite.op ⦋n⦌) x)).toOrderHom i =
      prismOrder ⦋k⦌ (SSet.prodStdSimplex.objEquiv x i) := rfl

instance prism_mono (k : SimplexCategory) : Mono (prism.{u} k) := by
  induction k using SimplexCategory.rec with
  | _ k =>
    rw [NatTrans.mono_iff_mono_app]
    intro q
    induction q using Opposite.rec with | op q =>
      induction q using SimplexCategory.rec with | h n =>
        apply (mono_iff_injective _).mpr
        intro x y hxy
        apply SSet.prodStdSimplex.objEquiv.injective
        apply OrderHom.ext
        funext i
        apply prismOrder_injective ⦋k⦌
        have h := congrArg (fun z ↦
            (SSet.stdSimplex.objEquiv z).toOrderHom i) hxy
        simpa only [prism_apply] using h

/-- The prism projection is literally the first Cartesian projection. -/
theorem prism_ret (k : SimplexCategory) :
    prism.{u} k ≫ SSet.stdSimplex.map (ret k) =
      fst (SSet.stdSimplex.obj k : SSet.{u}) (Δ[1] : SSet.{u}) := by
  induction k using SimplexCategory.rec with
  | _ k =>
    apply NatTrans.ext
    funext q x
    induction q using Opposite.rec with | op q =>
      induction q using SimplexCategory.rec with | h n =>
        apply SSet.stdSimplex.objEquiv.injective
        ext i : 3
        apply Fin.ext
        change ((prismOrder ⦋k⦌ (SSet.prodStdSimplex.objEquiv x i)).val / 2) =
          (SSet.prodStdSimplex.objEquiv x i).1.val
        have ht := (SSet.prodStdSimplex.objEquiv x i).2.isLt
        dsimp [prismOrder]
        omega

/-- The Cartesian inclusion of either full slice. -/
def ordinarySlice (k : SimplexCategory) (t : Fin 2) :
    (SSet.stdSimplex.obj k : SSet.{u}) ⟶ (SSet.stdSimplex.obj k : SSet.{u}) ⊗ Δ[1] :=
  lift (𝟙 (SSet.stdSimplex.obj k : SSet.{u}))
    (SSet.stdSimplex.map (SimplexCategory.const k ⦋1⦌ t))

theorem ordinarySlice_prism (k : SimplexCategory) (t : Fin 2) :
    ordinarySlice.{u} k t ≫ prism k = SSet.stdSimplex.map (slice k t) := by
  induction k using SimplexCategory.rec with
  | _ k =>
    apply NatTrans.ext
    funext q x
    induction q using Opposite.rec with | op q =>
      induction q using SimplexCategory.rec with | h n =>
        apply SSet.stdSimplex.objEquiv.injective
        ext i : 3
        apply Fin.ext
        change 2 * (x i).val + t.val = 2 * (x i).val + t.val
        rfl

/-- The vertical interval edge at a chosen vertex of `k`. -/
def verticalSection (k : SimplexCategory) (a : Fin (k.len + 1)) :
    (Δ[1] : SSet.{u}) ⟶ (SSet.stdSimplex.obj k : SSet.{u}) ⊗ Δ[1] :=
  lift (SSet.stdSimplex.map (SimplexCategory.const ⦋1⦌ k a))
    (𝟙 (Δ[1] : SSet.{u}))

theorem verticalSection_prism (k : SimplexCategory)
    (a : Fin (k.len + 1)) :
    verticalSection.{u} k a ≫ prism k = SSet.stdSimplex.map (edge k a) := by
  induction k using SimplexCategory.rec with
  | _ k =>
    apply NatTrans.ext
    funext q x
    induction q using Opposite.rec with | op q =>
      induction q using SimplexCategory.rec with | h n =>
        apply SSet.stdSimplex.objEquiv.injective
        ext i : 3
        apply Fin.ext
        change 2 * a.val + (x i).val = 2 * a.val + (x i).val
        rfl

/-- An ordinal map between standard simplices is Kan weak. -/
theorem standardMap_weak {k l : SimplexCategory} (j : k ⟶ l) :
    WeakEquivalence (SSet.stdSimplex.{u}.map j) := by
  let t (a : SimplexCategory) := CartesianMonoidalCategory.toUnit (SSet.stdSimplex.obj a : SSet.{u})
  have weak (a : SimplexCategory) : WeakEquivalence (t a) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
      (DaggerNativeCoherentCotensorResolutionWeak.simplex_parameter_GW a)
  haveI := weak k
  haveI := weak l
  exact weakEquivalence_of_postcomp_of_fac
    (show SSet.stdSimplex.map j ≫ t l = t k from
      CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _)

/-- The ordinary interleaved prism embedding is a Kan weak equivalence. -/
theorem prism_weak (k : SimplexCategory) : WeakEquivalence (prism.{u} k) := by
  haveI := standardMap_weak.{u} (ret k)
  haveI : WeakEquivalence (snd (Δ[1] : SSet.{u}) (SSet.stdSimplex.obj k : SSet.{u})) :=
    DaggerNativeContractibleSimplexParameter.simplexProjection_weakEquivalence 1 _
  haveI : WeakEquivalence (fst (SSet.stdSimplex.obj k : SSet.{u}) (Δ[1] : SSet.{u})) := by
    rw [← braiding_hom_snd]
    infer_instance
  exact weakEquivalence_of_postcomp_of_fac (prism_ret.{u} k)

end

end DaggerModels.PartII.JTInterleavedParameter
