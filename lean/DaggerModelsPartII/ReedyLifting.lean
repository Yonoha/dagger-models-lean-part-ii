import DaggerModelsPartII.ReedyDegreeLifting
import DaggerModelsPartII.ReedyExtendTransformation

/-!
# Reedy lifting from the relative maps

A lift at all lower degrees is extended through the next degree, and the
resulting compatible sequence gives a lift of the entire simplicial square.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe v u

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C] [HasLimitsOfSize.{0, 0} C]
  [HasColimitsOfSize.{0, 0} C]
  {X Y U V : SimplexCategoryᵒᵖ ⥤ C} {i : X ⟶ Y} {p : U ⟶ V}
  {a : X ⟶ U} {b : Y ⟶ V}

/-- A lift of the square in degrees strictly below `n`. -/
structure LiftBelow (i : X ⟶ Y) (p : U ⟶ V) (a : X ⟶ U) (b : Y ⟶ V) (n : ℕ) where
  hom : lowerDiagram n Y ⟶ lowerDiagram n U
  fac_left (s : BelowDegree n) : i.app s.obj ≫ hom.app s = a.app s.obj
  fac_right (s : BelowDegree n) : hom.app s ≫ p.app s.obj = b.app s.obj

variable (sq : CommSq a i p b)
  (h : ∀ n, HasLiftingProperty (relativeLatchingMap n i) (relativeMatchingMap n p))

include sq h in
/-- The new degree component of the lift, with its compatibility and triangles. -/
theorem exists_liftBelowDegree {n : ℕ} (prev : LiftBelow i p a b n) :
    ∃ L : DegreeExtension.Hom prev.hom (DegreeExtension.ofDiagram n Y)
        (DegreeExtension.ofDiagram n U),
      i.app (op ⦋n⦌) ≫ L.app = a.app (op ⦋n⦌) ∧
      L.app ≫ p.app (op ⦋n⦌) = b.app (op ⦋n⦌) := by
  have hl : Functor.whiskerLeft (belowDegree n).ι i ≫ prev.hom =
      Functor.whiskerLeft (belowDegree n).ι a := by
    ext s
    exact prev.fac_left s
  have hr : prev.hom ≫ Functor.whiskerLeft (belowDegree n).ι p =
      Functor.whiskerLeft (belowDegree n).ι b := by
    ext s
    exact prev.fac_right s
  exact exists_liftedDegree (DegreeExtension.Hom.ofDiagram i n)
    (DegreeExtension.Hom.ofDiagram p n) (DegreeExtension.Hom.ofDiagram a n)
    (DegreeExtension.Hom.ofDiagram b n) prev.hom hl hr
    (NatTrans.congr_app sq.w (op ⦋n⦌)) (h n)

/-- Extend the lift through one more degree. -/
def liftBelowStep {n : ℕ} (prev : LiftBelow i p a b n) : LiftBelow i p a b (n + 1) := by
  let e := exists_liftBelowDegree sq h prev
  let L := Classical.choose e
  refine ⟨extendDegreeTransformation L, ?_, ?_⟩
  · intro s
    change i.app s.obj ≫ extendDegreeApp L s = a.app s.obj
    by_cases hs : s.obj.unop.len < n
    · rw [extendDegreeApp_of_below L s hs]
      exact prev.fac_left ⟨s.obj, hs⟩
    · obtain rfl := eq_degreeTop_of_not_below s hs
      rw [extendDegreeApp_top]
      exact (Classical.choose_spec e).1
  · intro s
    change extendDegreeApp L s ≫ p.app s.obj = b.app s.obj
    by_cases hs : s.obj.unop.len < n
    · rw [extendDegreeApp_of_below L s hs]
      exact prev.fac_right ⟨s.obj, hs⟩
    · obtain rfl := eq_degreeTop_of_not_below s hs
      rw [extendDegreeApp_top]
      exact (Classical.choose_spec e).2

/-- Compatible lifts on the initial segments of the simplex category. -/
def liftBelow : (n : ℕ) → LiftBelow i p a b n
  | 0 =>
    { hom :=
        { app := fun s ↦ False.elim (Nat.not_lt_zero _ s.property)
          naturality := fun s _ _ ↦ False.elim (Nat.not_lt_zero _ s.property) }
      fac_left := fun s ↦ False.elim (Nat.not_lt_zero _ s.property)
      fac_right := fun s ↦ False.elim (Nat.not_lt_zero _ s.property) }
  | n + 1 => liftBelowStep sq h (liftBelow n)

/-- Successive lifts agree on the degrees already constructed. -/
theorem liftBelow_app_succ {n : ℕ} (s : SimplexCategoryᵒᵖ) (hs : s.unop.len < n) :
    (liftBelow sq h (n + 1)).hom.app ⟨s, Nat.lt_succ_of_lt hs⟩ =
      (liftBelow sq h n).hom.app ⟨s, hs⟩ :=
  extendDegreeApp_of_below _ _ hs

theorem liftBelow_app_stable (s : SimplexCategoryᵒᵖ) {k m : ℕ}
    (hk : s.unop.len < k) (hkm : k ≤ m) :
    (liftBelow sq h m).hom.app ⟨s, lt_of_lt_of_le hk hkm⟩ =
      (liftBelow sq h k).hom.app ⟨s, hk⟩ := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases h' : k ≤ m
    · exact (liftBelow_app_succ sq h s (lt_of_lt_of_le hk h')).trans (ih h')
    · have he : k = m + 1 := by omega
      subst k
      rfl

/-- The lift in every simplicial degree. -/
def reedyLift : Y ⟶ U where
  app s := (liftBelow sq h (s.unop.len + 1)).hom.app ⟨s, Nat.lt_succ_self _⟩
  naturality s t f := by
    let N := max s.unop.len t.unop.len + 1
    have hs : s.unop.len + 1 ≤ N := Nat.succ_le_succ (le_max_left _ _)
    have ht : t.unop.len + 1 ≤ N := Nat.succ_le_succ (le_max_right _ _)
    have hS := liftBelow_app_stable sq h s (Nat.lt_succ_self _) hs
    have hT := liftBelow_app_stable sq h t (Nat.lt_succ_self _) ht
    rw [← hS, ← hT]
    exact (liftBelow sq h N).hom.naturality (ObjectProperty.homMk
      (X := (⟨s, lt_of_lt_of_le (Nat.lt_succ_self _) hs⟩ : BelowDegree N))
      (Y := (⟨t, lt_of_lt_of_le (Nat.lt_succ_self _) ht⟩ : BelowDegree N)) f)

theorem reedyLift_fac_left : i ≫ reedyLift sq h = a := by
  ext s
  exact (liftBelow sq h (s.unop.len + 1)).fac_left ⟨s, Nat.lt_succ_self _⟩

theorem reedyLift_fac_right : reedyLift sq h ≫ p = b := by
  ext s
  exact (liftBelow sq h (s.unop.len + 1)).fac_right ⟨s, Nat.lt_succ_self _⟩

include h in
/-- Relative lifting in the coefficient category implies lifting of the simplicial maps. -/
theorem reedyLiftingOfRelativeMaps :
    HasLiftingProperty i p :=
  ⟨fun sq ↦ CommSq.HasLift.mk' ⟨reedyLift sq h, reedyLift_fac_left sq h,
    reedyLift_fac_right sq h⟩⟩

end

end DaggerModels.PartII
