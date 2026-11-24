import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Common least vertices for constraints on a finite ordinal

An equation after a monotone ordinal map cuts out an order-connected
set. Pairwise common solutions suffice for a common least solution.
-/

set_option autoImplicit false

open Set

namespace DaggerModels.PartII.JTFiniteOrdinalConstraints

variable {α : Type*} [LinearOrder α] [Finite α]

private theorem exists_least {s : Set α} (h : s.Nonempty) :
    ∃ a, IsLeast s a := by
  obtain ⟨a, ha, ha'⟩ := Set.exists_min_image s id s.toFinite h
  exact ⟨a, ha, fun _ hb ↦ ha' _ hb⟩

/-- A common least element exists if every pair of constraints intersects.
The empty collection uses the bottom element. -/
theorem exists_least_common [OrderBot α] {ι : Type*} (s : ι → Set α)
    (convex : ∀ i, (s i).OrdConnected) (pairs : ∀ i j, (s i ∩ s j).Nonempty) :
    ∃ a, IsLeast {x | ∀ i, x ∈ s i} a := by
  classical
  by_cases hi : Nonempty ι
  · let l (i : ι) : α := (exists_least (pairs i i |>.mono inter_subset_left)).choose
    have hl (i : ι) : IsLeast (s i) (l i) :=
      (exists_least (pairs i i |>.mono inter_subset_left)).choose_spec
    let S := Set.range l
    have hS : S.Nonempty := Set.range_nonempty l
    obtain ⟨a, ⟨i, rfl⟩, ha⟩ := Set.exists_max_image S id S.toFinite hS
    refine ⟨l i, ?_, ?_⟩
    · intro j
      obtain ⟨b, hb₁, hb₂⟩ := pairs i j
      have h₁ : l j ≤ l i := ha _ ⟨j, rfl⟩
      have h₂ : l i ≤ b := (hl i).2 hb₁
      exact (convex j).out (hl j).1 hb₂ ⟨h₁, h₂⟩
    · intro b hb
      exact (hl i).2 (hb i)
  · exact ⟨⊥, fun i ↦ (hi ⟨i⟩).elim, fun _ _ ↦ bot_le⟩

omit [Finite α] in
/-- The solutions to one equation under a monotone map form an interval. -/
theorem ordConnected_fiber {β : Type*} [PartialOrder β]
    (b : α →o β) (c : β) :
    ({x | b x = c} : Set α).OrdConnected := by
  letI : ({c} : Set β).OrdConnected := Set.ordConnected_singleton
  exact Set.ordConnected_preimage b (s := {c})

end DaggerModels.PartII.JTFiniteOrdinalConstraints
