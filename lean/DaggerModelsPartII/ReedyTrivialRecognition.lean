import DaggerModelsPartII.ReedyRelativeWfs
import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Recognizing relative trivial classes

The degree induction reduces the two recognition results to preservation
of the relevant lifting classes by matching and latching objects, using
only lower degrees at each step.
-/

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty Opposite Simplicial

universe v u

namespace DaggerModels.PartII

variable {C : Type u} [Category.{v} C]

section Matching

variable [HasLimitsOfSize.{0, 0} C]
variable {X Y : SimplexCategoryᵒᵖ ⥤ C} (f : X ⟶ Y) (n : ℕ)

/-- The projection of the relative matching map is the original component. -/
theorem relativeMatchingMap_comp_snd :
    relativeMatchingMap n f ≫ pullback.snd _ _ = f.app (op ⦋n⦌) :=
  pullback.lift_snd _ _ _

/-- Recognition of the matching class, reduced to the lower-degree limit calculation. -/
theorem reedyMatching_inf_levelwise_eq (Q W : MorphismProperty C)
    [W.HasTwoOutOfThreeProperty]
    [(Q ⊓ W).IsStableUnderBaseChange]
    (matching : ∀ (n : ℕ),
      (∀ m < n, (Q ⊓ W) (relativeMatchingMap m f)) →
        (Q ⊓ W) ((matchingFunctor n).map f)) :
    (reedyMatchingProperty Q ⊓ W.functorCategory SimplexCategoryᵒᵖ) f ↔
      reedyMatchingProperty (Q ⊓ W) f := by
  constructor
  · intro h n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have hs := (Q ⊓ W).pullback_snd ((matchingFunctor n).map f)
        ((matchingComparison n).app Y) (matching n ih)
      refine ⟨h.1 n, W.of_postcomp _ _ hs.2 ?_⟩
      rw [relativeMatchingMap_comp_snd]
      exact h.2 _
  · intro h
    refine ⟨fun n ↦ (h n).1, ?_⟩
    intro j
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, op ⦋n⦌ = j :=
      ⟨j.unop.len, congrArg op (SimplexCategory.ext _ _ rfl)⟩
    have hs := (Q ⊓ W).pullback_snd ((matchingFunctor n).map f)
      ((matchingComparison n).app Y) (matching n fun m _ ↦ h m)
    rw [← relativeMatchingMap_comp_snd f n]
    exact W.comp_mem _ _ (h n).2 hs.2

end Matching

section Latching

variable [HasColimitsOfSize.{0, 0} C]
variable {X Y : SimplexCategoryᵒᵖ ⥤ C} (f : X ⟶ Y) (n : ℕ)

/-- Restricting the relative latching map to the first summand recovers the component. -/
theorem inl_comp_relativeLatchingMap :
    pushout.inl _ _ ≫ relativeLatchingMap n f = f.app (op ⦋n⦌) :=
  pushout.inl_desc _ _ _

/-- Recognition of the latching class, reduced to the lower-degree colimit calculation. -/
theorem reedyLatching_inf_levelwise_eq (P W : MorphismProperty C)
    [W.HasTwoOutOfThreeProperty] [(P ⊓ W).IsStableUnderCobaseChange]
    (latching : ∀ (n : ℕ),
      (∀ m < n, (P ⊓ W) (relativeLatchingMap m f)) →
        (P ⊓ W) ((latchingFunctor n).map f)) :
    (reedyLatchingProperty P ⊓ W.functorCategory SimplexCategoryᵒᵖ) f ↔
      reedyLatchingProperty (P ⊓ W) f := by
  constructor
  · intro h n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have hs := (P ⊓ W).pushout_inl ((latchingComparison n).app X)
        ((latchingFunctor n).map f) (latching n ih)
      refine ⟨h.1 n, W.of_precomp _ _ hs.2 ?_⟩
      rw [inl_comp_relativeLatchingMap]
      exact h.2 _
  · intro h
    refine ⟨fun n ↦ (h n).1, ?_⟩
    intro j
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, op ⦋n⦌ = j :=
      ⟨j.unop.len, congrArg op (SimplexCategory.ext _ _ rfl)⟩
    have hs := (P ⊓ W).pushout_inl ((latchingComparison n).app X)
      ((latchingFunctor n).map f) (latching n fun m _ ↦ h m)
    rw [← inl_comp_relativeLatchingMap f n]
    exact W.comp_mem _ _ hs.2 (h n).2

end Latching

end DaggerModels.PartII
