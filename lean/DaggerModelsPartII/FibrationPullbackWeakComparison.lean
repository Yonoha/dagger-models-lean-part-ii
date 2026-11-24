import NativeSSetFibrationsOverBaseWeakPullbacks
import SSetRightProper

/-! Weak comparison of strict pullbacks of Kan fibrations. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.FibrationPullbackWeakComparison

open DaggerNativeSSetFibrationsOverBaseWeakPullbacks

noncomputable section

universe u

/-- A map of pullback spans, weak at all three terms, induces a weak map of
pullbacks when the chosen leg is a fibration in each span. -/
theorem weak_of_pullback_map {X' Y' B' X Y B : SSet.{u}}
    (p' : X' ⟶ B') (q' : Y' ⟶ B') (p : X ⟶ B) (q : Y ⟶ B)
    (a : X' ⟶ X) (b : Y' ⟶ Y) (c : B' ⟶ B)
    (ha : a ≫ p = p' ≫ c) (hb : b ≫ q = q' ≫ c)
    [Fibration p'] [Fibration p] [WeakEquivalence a] [WeakEquivalence b] [WeakEquivalence c] :
    WeakEquivalence (pullback.map p' q' p q a b c ha.symm hb.symm) := by
  let p₀ := pullback.snd p c
  let k : X' ⟶ pullback p c := pullback.lift a p' ha
  have hk : k ≫ p₀ = p' := pullback.lift_snd _ _ _
  haveI : WeakEquivalence (pullback.fst p c) :=
    DaggerSSetRightProper.weakEquivalence_of_isPullback (IsPullback.of_hasPullback p c)
  haveI : WeakEquivalence k := weakEquivalence_of_postcomp_of_fac (pullback.lift_fst _ _ _)
  letI : Fibration p₀ := inferInstanceAs (Fibration (pullback.snd p c))
  let v := mapOver p' p₀ k hk q'
  haveI : WeakEquivalence v := mapOver_weakEquivalence p' p₀ k hk q'
  have H := (IsPullback.of_hasPullback p₀ q').paste_horiz (IsPullback.of_hasPullback p c)
  have H' : IsPullback (pullback.fst p₀ q' ≫ pullback.fst p c)
      (pullback.snd p₀ q') p (b ≫ q) := by
    rw [hb]
    exact H
  let t : pullback p₀ q' ⟶ pullback p q := pullback.lift
    (pullback.fst p₀ q' ≫ pullback.fst p c) (pullback.snd p₀ q' ≫ b)
    (H'.w.trans (Category.assoc _ _ _).symm)
  have ht : IsPullback t (pullback.snd p₀ q') (pullback.snd p q) b :=
    IsPullback.of_right (h₁₂ := pullback.fst p q)
      ((show t ≫ pullback.fst p q = _ from pullback.lift_fst _ _ _) ▸ H')
      (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback p q)
  haveI : WeakEquivalence t := DaggerSSetRightProper.weakEquivalence_of_isPullback ht
  have hcomp : v ≫ t = pullback.map p' q' p q a b c ha.symm hb.symm := by
    apply pullback.hom_ext
    · simp only [t, pullback.map, Category.assoc, pullback.lift_fst]
      rw [← Category.assoc v, mapOver_fst, Category.assoc]
      simp only [k, pullback.lift_fst]
    · simp only [t, v, mapOver, pullback.map, Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, pullback.lift_snd]
  rw [← hcomp]
  infer_instance

end

end DaggerModels.PartII.FibrationPullbackWeakComparison
