import NativeSSetFibrationSquareFibreWeak
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Weak comparison of pullbacks of actual Kan fibrations

The original weak-square theorem allows an unchanged point object. Here the
point object is also allowed to change by a weak equivalence. Its comparison
is a base change of that weak map along a Kan fibration, so the retained
right-properness theorem applies. No fibrancy of the base or point is assumed.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.SSetWeakPullbackComparison

noncomputable section

def pointMap {Y D K L : SSet.{u}} (q : Y ⟶ D) (b : K ⟶ D) (d : L ⟶ D)
    (k : K ⟶ L) (hk : b = k ≫ d) : pullback q b ⟶ pullback q d :=
  pullback.lift (pullback.fst q b) (pullback.snd q b ≫ k) (by
    rw [Category.assoc, ← hk]
    exact pullback.condition)

theorem pointMap_fst {Y D K L : SSet.{u}} (q : Y ⟶ D) (b : K ⟶ D) (d : L ⟶ D)
    (k : K ⟶ L) (hk : b = k ≫ d) :
    pointMap q b d k hk ≫ pullback.fst q d = pullback.fst q b := by
  simp only [pointMap, pullback.lift_fst]

theorem pointMap_snd {Y D K L : SSet.{u}} (q : Y ⟶ D) (b : K ⟶ D) (d : L ⟶ D)
    (k : K ⟶ L) (hk : b = k ≫ d) :
    pointMap q b d k hk ≫ pullback.snd q d = pullback.snd q b ≫ k := by
  simp only [pointMap, pullback.lift_snd]

theorem pointMap_isPullback {Y D K L : SSet.{u}}
    (q : Y ⟶ D) (b : K ⟶ D) (d : L ⟶ D)
    (k : K ⟶ L) (hk : b = k ≫ d) :
    IsPullback (pointMap q b d k hk) (pullback.snd q b) (pullback.snd q d) k := by
  have outer : IsPullback
      (pointMap q b d k hk ≫ pullback.fst q d) (pullback.snd q b) q (k ≫ d) := by
    simpa only [pointMap_fst, ← hk] using IsPullback.of_hasPullback q b
  exact outer.of_right (pointMap_snd q b d k hk) (IsPullback.of_hasPullback q d)

theorem pointMap_weak {Y D K L : SSet.{u}}
    (q : Y ⟶ D) (b : K ⟶ D) (d : L ⟶ D)
    (k : K ⟶ L) (hk : b = k ≫ d) [Fibration q] [WeakEquivalence k] :
    WeakEquivalence (pointMap q b d k hk) :=
  DaggerSSetRightProper.weakEquivalence_of_isPullback (pointMap_isPullback q b d k hk)

/-- The actual comparison of the original total, base, and point maps. -/
def comparison {X Y B D K L : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ D)
    (f : X ⟶ Y) (g : B ⟶ D) (h : p ≫ g = f ≫ q)
    (b : K ⟶ B) (d : L ⟶ D) (k : K ⟶ L) (hk : b ≫ g = k ≫ d) :
    pullback p b ⟶ pullback q d :=
  pullback.lift (pullback.fst p b ≫ f) (pullback.snd p b ≫ k) (by
    rw [Category.assoc, ← h, pullback.condition_assoc, hk, Category.assoc])

theorem comparison_fst {X Y B D K L : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ D)
    (f : X ⟶ Y) (g : B ⟶ D) (h : p ≫ g = f ≫ q)
    (b : K ⟶ B) (d : L ⟶ D) (k : K ⟶ L) (hk : b ≫ g = k ≫ d) :
    comparison p q f g h b d k hk ≫ pullback.fst q d =
      pullback.fst p b ≫ f := by
  simp only [comparison, pullback.lift_fst]

theorem comparison_snd {X Y B D K L : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ D)
    (f : X ⟶ Y) (g : B ⟶ D) (h : p ≫ g = f ≫ q)
    (b : K ⟶ B) (d : L ⟶ D) (k : K ⟶ L) (hk : b ≫ g = k ≫ d) :
    comparison p q f g h b d k hk ≫ pullback.snd q d =
      pullback.snd p b ≫ k := by
  simp only [comparison, pullback.lift_snd]

/-- Weak total, base, and point maps preserve the pullback comparison
when both original projections are Kan fibrations. -/
theorem comparison_weak {X Y B D K L : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ D)
    (f : X ⟶ Y) (g : B ⟶ D) (h : p ≫ g = f ≫ q)
    (b : K ⟶ B) (d : L ⟶ D) (k : K ⟶ L) (hk : b ≫ g = k ≫ d)
    [Fibration p] [Fibration q] [WeakEquivalence f] [WeakEquivalence g]
    [WeakEquivalence k] : WeakEquivalence (comparison p q f g h b d k hk) := by
  let a := DaggerNativeSSetFibrationSquareFibreWeak.fibreMap
    p q f g h b (b ≫ g) rfl
  let t := pointMap q (b ≫ g) d k hk
  have : WeakEquivalence a :=
    DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_weakEquivalence
      p q f g h b (b ≫ g) rfl
  have : WeakEquivalence t := pointMap_weak q (b ≫ g) d k hk
  have ht : a ≫ t = comparison p q f g h b d k hk := by
    apply pullback.hom_ext
    · simp only [Category.assoc, t, pointMap_fst,
        DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_fst, a, comparison_fst]
    · simp only [Category.assoc, t, pointMap_snd, a, comparison_snd]
      rw [← Category.assoc, DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_snd]
  rw [← ht]
  infer_instance

#print axioms pointMap_isPullback
#print axioms pointMap_weak
#print axioms comparison_weak

end
end DaggerModels.PartII.SSetWeakPullbackComparison
