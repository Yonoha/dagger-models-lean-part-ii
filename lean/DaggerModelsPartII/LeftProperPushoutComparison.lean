import Mathlib.AlgebraicTopology.ModelCategory.Basic
import Mathlib.AlgebraicTopology.ModelCategory.Instances
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-! Homotopy invariance of pushouts of spans with one cofibration leg. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

universe v u

namespace DaggerModels.PartII

variable {C : Type u} [Category.{v} C] [ModelCategory C]

local instance : (trivialCofibrations C).IsStableUnderCobaseChange := by
  rw [← llp_eq_of_wfs (trivialCofibrations C) (fibrations C)]
  infer_instance

private theorem changeSpanLeg_isPushout {A B D T : C} {i : A ⟶ B} {k : A ⟶ D}
    (a : B ⟶ T) :
    IsPushout a (pushout.inl i k) (pushout.inl (i ≫ a) k)
      (pushout.map i k (i ≫ a) k a (𝟙 D) (𝟙 A) (by simp) (by simp)) := by
  let m := pushout.map i k (i ≫ a) k a (𝟙 D) (𝟙 A) (by simp) (by simp)
  have h₁ : a ≫ pushout.inl (i ≫ a) k = pushout.inl i k ≫ m :=
    (pushout.inl_desc _ _ _).symm
  have h₂ : pushout.inr i k ≫ m = pushout.inr (i ≫ a) k := by simp [m]
  apply (IsPushout.of_hasPushout i k).paste_horiz_iff h₁ |>.mp
  rw [h₂]
  exact IsPushout.of_hasPushout _ _

private theorem weak_pushout_changeLeg {A B D T : C} {i : A ⟶ B} {j : A ⟶ T}
    (k : A ⟶ D) (a : B ⟶ T) (ha : i ≫ a = j)
    (hi : cofibrations C i) (hj : cofibrations C j) (hw : weakEquivalences C a) :
    weakEquivalences C
      (pushout.map i k j k a (𝟙 D) (𝟙 A) (by simpa using ha) (by simp)) := by
  let s : pushout i j ⟶ T := pushout.desc a (𝟙 T) (by simpa using ha)
  let f := factorizationData (cofibrations C) (trivialFibrations C) s
  let x := pushout.inl i j ≫ f.i
  let y := pushout.inr i j ≫ f.i
  have hx : x ≫ f.p = a := by simp only [x, Category.assoc, f.fac, s, pushout.inl_desc]
  have hy : y ≫ f.p = 𝟙 T := by simp only [y, Category.assoc, f.fac, s, pushout.inr_desc]
  have hyx : j ≫ y = i ≫ x := by simp only [x, y, ← Category.assoc, pushout.condition]
  have hx' : trivialCofibrations C x := ⟨(cofibrations C).comp_mem _ _
    ((cofibrations C).of_isPushout (IsPushout.of_hasPushout i j) hj) f.hi,
    (weakEquivalences C).of_postcomp _ _ f.hp.2 (hx.symm ▸ hw)⟩
  have hy' : trivialCofibrations C y := ⟨(cofibrations C).comp_mem _ _
    ((cofibrations C).of_isPushout (IsPushout.of_hasPushout i j).flip hi) f.hi,
    (weakEquivalences C).of_postcomp _ _ f.hp.2 (hy.symm ▸ (weakEquivalences C).id_mem _)⟩
  let m := pushout.map i k j k a (𝟙 D) (𝟙 A) (by simpa using ha) (by simp)
  let mx := pushout.map i k (i ≫ x) k x (𝟙 D) (𝟙 A) (by simp) (by simp)
  let my := pushout.map j k (i ≫ x) k y (𝟙 D) (𝟙 A) (by simpa using hyx) (by simp)
  let mp := pushout.map (i ≫ x) k j k f.p (𝟙 D) (𝟙 A) (by simpa [hx] using ha) (by simp)
  have hmx : trivialCofibrations C mx :=
    (trivialCofibrations C).of_isPushout (changeSpanLeg_isPushout x).flip hx'
  have hmy : trivialCofibrations C my := by
    have aux (z : A ⟶ f.Z) (hz : j ≫ y = z) :
        trivialCofibrations C
          (pushout.map j k z k y (𝟙 D) (𝟙 A) (by simpa using hz) (by simp)) := by
      subst z
      exact (trivialCofibrations C).of_isPushout
        (changeSpanLeg_isPushout (i := j) (k := k) y).flip hy'
    exact aux _ hyx
  have hmp : weakEquivalences C mp := by
    apply (weakEquivalences C).of_precomp _ _ hmy.2
    have hh : my ≫ mp = 𝟙 _ := by
      apply pushout.hom_ext <;> simp [my, mp, Category.assoc, ← Category.assoc y f.p, hy]
    rw [hh]
    exact (weakEquivalences C).id_mem _
  have hm : mx ≫ mp = m := by
    apply pushout.hom_ext <;> simp [mx, mp, m, Category.assoc, ← Category.assoc x f.p, hx]
  change weakEquivalences C m
  exact hm ▸ (weakEquivalences C).comp_mem _ _ hmx.2 hmp

/-- A map of pushout squares is weak on the apex if it is weak at the three
span vertices and the same leg of each span is a cofibration. -/
theorem weak_of_pushoutComparison
    (leftProper : ∀ {A B D P : C} {i : A ⟶ B} {k : A ⟶ D} {l : B ⟶ P} {r : D ⟶ P},
      IsPushout i k l r → cofibrations C i → weakEquivalences C k → weakEquivalences C l)
    {A B D P A' B' D' P' : C}
    {i : A ⟶ B} {k : A ⟶ D} {l : B ⟶ P} {r : D ⟶ P}
    {i' : A' ⟶ B'} {k' : A' ⟶ D'} {l' : B' ⟶ P'} {r' : D' ⟶ P'}
    (sq : IsPushout i k l r) (sq' : IsPushout i' k' l' r')
    (hi : cofibrations C i) (hi' : cofibrations C i')
    (a : A ⟶ A') (b : B ⟶ B') (c : D ⟶ D') (d : P ⟶ P')
    (h₁ : i ≫ b = a ≫ i') (h₂ : k ≫ c = a ≫ k')
    (h₃ : l ≫ d = b ≫ l') (h₄ : r ≫ d = c ≫ r')
    (ha : weakEquivalences C a) (hb : weakEquivalences C b) (hc : weakEquivalences C c) :
    weakEquivalences C d := by
  let t := pushout.inr i a
  let s := pushout.inl i a
  let q := pushout.desc b i' h₁
  have hq : t ≫ q = i' := pushout.inr_desc _ _ _
  have hsq : s ≫ q = b := pushout.inl_desc _ _ _
  have hsw := leftProper (IsPushout.of_hasPushout i a) hi ha
  have hqw : weakEquivalences C q :=
    (weakEquivalences C).of_precomp _ _ hsw (hsq.symm ▸ hb)
  have ht : cofibrations C t := (cofibrations C).of_isPushout
    (IsPushout.of_hasPushout i a).flip hi
  let m := sq.desc (s ≫ pushout.inl t k') (c ≫ pushout.inr t k') (by
    rw [← Category.assoc, pushout.condition, Category.assoc, pushout.condition,
      ← Category.assoc, ← h₂, Category.assoc])
  have hright : r ≫ m = c ≫ pushout.inr t k' := sq.inr_desc _ _ _
  have hleft : l ≫ m = s ≫ pushout.inl t k' := sq.inl_desc _ _ _
  have hpaste' : IsPushout i (k ≫ c) (s ≫ pushout.inl t k') (pushout.inr t k') := by
    rw [h₂]
    exact (IsPushout.of_hasPushout i a).paste_vert (IsPushout.of_hasPushout t k')
  have hm : IsPushout r c m (pushout.inr t k') :=
    (show IsPushout i (k ≫ c) (l ≫ m) (pushout.inr t k') by rw [hleft]; exact hpaste').of_top
      hright sq
  have hr : cofibrations C r := (cofibrations C).of_isPushout sq.flip hi
  have hmw := leftProper hm hr hc
  let p := pushout.map t k' i' k' q (𝟙 D') (𝟙 A') (by simpa using hq) (by simp)
  have hpw := weak_pushout_changeLeg k' q hq ht hi' hqw
  let e := sq'.isoPushout
  have hfac : m ≫ p = d ≫ e.hom := by
    apply sq.hom_ext
    · rw [← Category.assoc, hleft, Category.assoc, ← Category.assoc l, h₃, Category.assoc]
      simp [p, ← Category.assoc s q, hsq, e]
    · rw [← Category.assoc, hright, Category.assoc, ← Category.assoc r, h₄, Category.assoc]
      simp [p, e]
  exact ((weakEquivalences C).cancel_right_of_respectsIso _ e.hom).mp
    (hfac ▸ (weakEquivalences C).comp_mem _ _ hmw hpw)

end DaggerModels.PartII
