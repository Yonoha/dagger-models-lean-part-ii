import Mathlib.CategoryTheory.LiftingProperties.Basic
import Mathlib.CategoryTheory.Limits.Cones

/-! Degree induction for lifts of cones over inverse diagrams. -/

set_option autoImplicit false

open CategoryTheory Limits

universe v u v' u'

namespace DaggerModels.PartII

variable {J : Type u'} [Category.{v'} J] {C : Type u} [Category.{v} C]
  {X Y : J ⥤ C} {A B : C} (i : A ⟶ B) (p : X ⟶ Y)
  (a : (Functor.const J).obj A ⟶ X) (b : (Functor.const J).obj B ⟶ Y)
  (degree : J → ℕ)

/-- A lift of the cone square on the objects below the stated bound. -/
structure ConeLiftBelow (k : ℕ) where
  app (s : J) (hs : degree s < k) : B ⟶ X.obj s
  fac_left (s : J) (hs : degree s < k) : i ≫ app s hs = a.app s
  fac_right (s : J) (hs : degree s < k) : app s hs ≫ p.app s = b.app s
  naturality {s t : J} (f : s ⟶ t) (hs : degree s < k) (ht : degree t < k) :
    app s hs ≫ X.map f = app t ht

variable {i p a b degree}

/-- The conditions on the new leg at an object of degree `k`. -/
structure ConeLiftLeg {k : ℕ} (prev : ConeLiftBelow i p a b degree k) (s : J) where
  hom : B ⟶ X.obj s
  fac_left : i ≫ hom = a.app s
  fac_right : hom ≫ p.app s = b.app s
  naturality {t : J} (f : s ⟶ t) (ht : degree t < k) :
    hom ≫ X.map f = prev.app t ht

noncomputable section

variable
  (decreases : ∀ {s t : J} (f : s ⟶ t),
    degree t < degree s ∨ ∃ h : s = t, f = eqToHom h)
  (extend : ∀ {k} (prev : ConeLiftBelow i p a b degree k) (s : J),
    degree s = k → Nonempty (ConeLiftLeg prev s))

private def coneLiftLegAtSucc {k : ℕ} (prev : ConeLiftBelow i p a b degree k)
    (s : J) (hs : degree s < k + 1) : B ⟶ X.obj s :=
  if h : degree s < k then prev.app s h
  else (Classical.choice (extend prev s (by omega))).hom

private def coneLiftBelowSucc {k : ℕ} (prev : ConeLiftBelow i p a b degree k) :
    ConeLiftBelow i p a b degree (k + 1) where
  app := coneLiftLegAtSucc extend prev
  fac_left s hs := by
    unfold coneLiftLegAtSucc
    split
    · apply prev.fac_left
    · apply ConeLiftLeg.fac_left
  fac_right s hs := by
    unfold coneLiftLegAtSucc
    split
    · apply prev.fac_right
    · apply ConeLiftLeg.fac_right
  naturality f hs ht := by
    rcases decreases f with h | ⟨rfl, rfl⟩
    · have htarget : degree _ < k := lt_of_lt_of_le h (Nat.le_of_lt_succ hs)
      unfold coneLiftLegAtSucc
      rw [dif_pos htarget]
      split
      · apply prev.naturality
      · apply ConeLiftLeg.naturality
    · simp

/-- Compatible legs through degree `k - 1`. -/
def coneLiftBelow : (k : ℕ) → ConeLiftBelow i p a b degree k
  | 0 =>
    { app := fun _ hs ↦ (Nat.not_lt_zero _ hs).elim
      fac_left := fun _ hs ↦ (Nat.not_lt_zero _ hs).elim
      fac_right := fun _ hs ↦ (Nat.not_lt_zero _ hs).elim
      naturality := fun _ hs _ ↦ (Nat.not_lt_zero _ hs).elim }
  | k + 1 => coneLiftBelowSucc decreases extend (coneLiftBelow k)

end

end DaggerModels.PartII
