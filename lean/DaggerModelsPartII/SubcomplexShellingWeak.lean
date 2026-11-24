import NativeFiniteSubcomplexWeakGluing

/-!
# Weak augmentation gluing along finite subcomplex shellings

Every weak-equivalence assertion below concerns the restriction of one
fixed map to a subcomplex. The pushout square is the native bicartesian
square of an intersection and union of simplicial subcomplexes.
-/

set_option autoImplicit false

open CategoryTheory Limits Simplicial
open DaggerNativeJoyalMappingTest

namespace DaggerModels.PartII.SubcomplexShellingWeak

noncomputable section

universe u

variable {X Y : SSet.{u}} (p : X ⟶ Y)

/-- Gluing two weak restrictions of the same map, when their overlap
also has a weak restriction. -/
theorem union_weak (A B : X.Subcomplex)
    (hA : weakCategoricalEquivalences (A.ι ≫ p))
    (hB : weakCategoricalEquivalences (B.ι ≫ p))
    (hI : weakCategoricalEquivalences ((A ⊓ B).ι ≫ p)) :
    weakCategoricalEquivalences ((A ⊔ B).ι ≫ p) := by
  let i : (A ⊓ B : X.Subcomplex).toSSet ⟶ (A : SSet.{u}) :=
    SSet.Subcomplex.homOfLE inf_le_left
  let j : (B : SSet.{u}) ⟶ (A ⊔ B : X.Subcomplex).toSSet :=
    SSet.Subcomplex.homOfLE le_sup_right
  have hi : weakCategoricalEquivalences i := by
    apply weakCategoricalEquivalences.of_postcomp i (A.ι ≫ p) hA
    dsimp [i]
    simpa only [Category.assoc, SSet.Subcomplex.homOfLE_ι] using hI
  have sq : SSet.Subcomplex.BicartSq (A ⊓ B) A B (A ⊔ B) :=
    ⟨rfl, rfl⟩
  have hj : weakCategoricalEquivalences j := by
    dsimp [j]
    exact DaggerNativeOriginalWeakMonoPushout.weak_of_isPushout
      sq.isPushout hi
  apply weakCategoricalEquivalences.of_precomp j ((A ⊔ B).ι ≫ p) hj
  dsimp [j]
  simpa only [Category.assoc, SSet.Subcomplex.homOfLE_ι] using hB

/-- The first `n+1` cells of an ordered family, including cell zero. -/
def initialUnion (F : ℕ → X.Subcomplex) (n : ℕ) : X.Subcomplex :=
  (Finset.range (n + 1)).sup F

theorem initialUnion_zero (F : ℕ → X.Subcomplex) :
    initialUnion F 0 = F 0 := by
  simp [initialUnion]

theorem initialUnion_succ (F : ℕ → X.Subcomplex) (n : ℕ) :
    initialUnion F (n + 1) = initialUnion F n ⊔ F (n + 1) := by
  change (Finset.range ((n + 1) + 1)).sup F =
    (Finset.range (n + 1)).sup F ⊔ F (n + 1)
  rw [Finset.range_add_one, Finset.sup_insert]
  ac_rfl

/-- Finite ordered gluing: each cell and its exact overlap with the
preceding union are weak over the same target map. The zero-cell case
uses its own weak restriction and has no empty-source premise. -/
theorem prefix_weak (F : ℕ → X.Subcomplex) (N : ℕ)
    (hCell : ∀ n ≤ N,
      weakCategoricalEquivalences ((F n).ι ≫ p))
    (hOverlap : ∀ n < N,
      weakCategoricalEquivalences
        ((F (n + 1) ⊓ initialUnion F n).ι ≫ p)) :
    weakCategoricalEquivalences ((initialUnion F N).ι ≫ p) := by
  revert hCell hOverlap
  induction N with
  | zero =>
    intro hCell hOverlap
    rw [initialUnion_zero]
    exact hCell 0 (Nat.le_refl 0)
  | succ n ih =>
    intro hCell hOverlap
    have hOld : ∀ k ≤ n,
        weakCategoricalEquivalences ((F k).ι ≫ p) := by
      intro k hk
      exact hCell k (Nat.le_trans hk (Nat.le_succ n))
    have hOldOverlap : ∀ k < n,
        weakCategoricalEquivalences
          ((F (k + 1) ⊓ initialUnion F k).ι ≫ p) := by
      intro k hk
      exact hOverlap k (Nat.lt_succ_of_lt hk)
    have hPrev := ih hOld hOldOverlap
    have hNext := hCell (n + 1) (Nat.le_refl _)
    have hMeet := hOverlap n (Nat.lt_succ_self n)
    rw [inf_comm (F (n + 1)) (initialUnion F n)] at hMeet
    rw [initialUnion_succ]
    exact union_weak p (initialUnion F n) (F (n + 1))
      hPrev hNext hMeet

end
end DaggerModels.PartII.SubcomplexShellingWeak
