import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Comparing vertical maps through two natural weak spans

Mathlib's two-out-of-three cancellation identifies the property of either
outer vertical map with the property of the same middle vertical map.
The middle map is not assumed weak. The two actual commuting squares
and all four original span legs are retained as explicit arguments.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory

namespace DaggerModels.PartII.WeakSpanMorphismTransfer

universe v u

variable {C : Type u} [Category.{v} C] {S A B S' A' B' : C}

/-- A commuting map of spans whose four legs satisfy the original
two-out-of-three property transfers that property between its outer maps. -/
theorem property_iff (P : MorphismProperty C) [P.HasTwoOutOfThreeProperty]
    (l : S ⟶ A) (r : S ⟶ B) (l' : S' ⟶ A') (r' : S' ⟶ B')
    (f : A ⟶ A') (g : B ⟶ B') (t : S ⟶ S')
    (hl : P l) (hr : P r) (hl' : P l') (hr' : P r')
    (hleft : l ≫ f = t ≫ l') (hright : r ≫ g = t ≫ r') :
    P f ↔ P g := by
  calc
    P f ↔ P (l ≫ f) := (P.precomp_iff l f hl).symm
    _ ↔ P (t ≫ l') := by rw [hleft]
    _ ↔ P t := P.postcomp_iff t l' hl'
    _ ↔ P (t ≫ r') := (P.postcomp_iff t r' hr').symm
    _ ↔ P (r ≫ g) := by rw [hright]
    _ ↔ P g := P.precomp_iff r g hr

#print axioms property_iff

end DaggerModels.PartII.WeakSpanMorphismTransfer
