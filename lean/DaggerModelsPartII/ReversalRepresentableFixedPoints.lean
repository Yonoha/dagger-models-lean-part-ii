import DaggerModels.ReverseSimplex

/-!
# Fixed points of reversal on actual representables

The action on `ReverseSimplex` representables is postcomposition with the
actual finite-ordinal reversal. Constant functions are single morphisms in
this category, independent of a choice of orientation.
-/

set_option autoImplicit false

open CategoryTheory

namespace DaggerModels.PartII.ReversalRepresentableFixedPoints

open ReverseSimplex

/-- The actual representable flip is postcomposition with target reversal. -/
def flip {k l : ReverseSimplex} (f : k ⟶ l) : k ⟶ l :=
  f ≫ reversal l

@[simp] theorem flip_apply {k l : ReverseSimplex} (f : k ⟶ l)
    (i : Fin (k.len + 1)) : (flip f).toFun i = (f.toFun i).rev := rfl

@[simp] theorem flip_flip {k l : ReverseSimplex} (f : k ⟶ l) :
    flip (flip f) = f := by
  simp only [flip, Category.assoc, reversal_comp_reversal, Category.comp_id]

/-- Fixedness is exactly the condition that every value is a fixed point of
the target ordinal reversal. -/
theorem flip_fixed_iff {k l : ReverseSimplex} (f : k ⟶ l) :
    flip f = f ↔ ∀ i : Fin (k.len + 1), (f.toFun i).rev = f.toFun i := by
  constructor
  · intro h i
    exact congrArg (fun g : k ⟶ l ↦ g.toFun i) h
  · intro h
    apply Hom.ext
    intro i
    exact h i

/-- A fixed value in `[l]` must have coordinate exactly halfway between its
endpoints. -/
theorem rev_fixed_iff_twice_val {l : ℕ} (j : Fin (l + 1)) :
    j.rev = j ↔ 2 * j.val = l := by
  constructor
  · intro h
    have hj := congrArg Fin.val h
    simp only [Fin.val_rev] at hj
    omega
  · intro h
    apply Fin.ext
    simp only [Fin.val_rev]
    omega

/-- No representable element is fixed when the target length is odd. -/
theorem no_fixed_odd (k r : ℕ) (f : (⟨k⟩ : ReverseSimplex) ⟶ ⟨2 * r + 1⟩) :
    flip f ≠ f := by
  intro h
  have hv := (rev_fixed_iff_twice_val (f.toFun (0 : Fin (k + 1)))).mp
    ((flip_fixed_iff f).mp h 0)
  change 2 * (f.toFun (0 : Fin (k + 1))).val = 2 * r + 1 at hv
  omega

/-- The odd-length formulation without a chosen half-length. -/
theorem no_fixed_of_odd (k l : ℕ) (hl : Odd l)
    (f : (⟨k⟩ : ReverseSimplex) ⟶ ⟨l⟩) : flip f ≠ f := by
  obtain ⟨r, rfl⟩ := odd_iff_exists_bit1.mp hl
  exact no_fixed_odd k r f

/-- In even target length, a fixed map is precisely the constant map at the
middle vertex. -/
theorem fixed_iff_middle_constant (k r : ℕ)
    (f : (⟨k⟩ : ReverseSimplex) ⟶ ⟨2 * r⟩) :
    flip f = f ↔
      ∀ i : Fin (k + 1), f.toFun i = (⟨r, by omega⟩ : Fin (2 * r + 1)) := by
  constructor
  · intro h i
    have hv := (rev_fixed_iff_twice_val (f.toFun i)).mp ((flip_fixed_iff f).mp h i)
    change 2 * (f.toFun i).val = 2 * r at hv
    apply Fin.ext
    change (f.toFun i).val = r
    omega
  · intro h
    apply (flip_fixed_iff f).mpr
    intro i
    rw [h i]
    apply (rev_fixed_iff_twice_val _).mpr
    simp

/-- A fixed map into an even ordinal of positive even length omits both
outer vertices. -/
theorem fixed_omits_endpoints (k r : ℕ) (hr : 1 ≤ r)
    (f : (⟨k⟩ : ReverseSimplex) ⟶ ⟨2 * r⟩) (hf : flip f = f)
    (i : Fin (k + 1)) :
    (f.toFun i).val ≠ 0 ∧ (f.toFun i).val ≠ 2 * r := by
  have h := (fixed_iff_middle_constant k r f).mp hf i
  have hv := congrArg Fin.val h
  change (f.toFun i).val = r at hv
  constructor <;> intro heq <;> omega

end DaggerModels.PartII.ReversalRepresentableFixedPoints
