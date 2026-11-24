import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# The arrow retract associated to a strict section

A strict section is an actual arrow retract of the opposite composite.
The existing Mathlib retract closure therefore applies without a new
two-out-of-six axiom or a change to any endpoint-dependent mapping space.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory

namespace DaggerModels.PartII.SplitSectionArrowRetract

universe v u

variable {C : Type u} [Category.{v} C] {A B : C}

/-- The section arrow retains its original source and target. -/
def sectionRetract (f : A ⟶ B) (g : B ⟶ A) (h : f ≫ g = 𝟙 A) :
    RetractArrow f (g ≫ f) where
  i := Arrow.homMk f (𝟙 B) (by
    change f ≫ (g ≫ f) = f ≫ 𝟙 B
    rw [← Category.assoc, h]
    simp)
  r := Arrow.homMk g (𝟙 B) (by simp)
  retract := by ext <;> simp [h]

/-- Any existing retract-stable morphism property passes from the
opposite composite to its actual strict section. -/
theorem property_section (P : MorphismProperty C) [P.IsStableUnderRetracts]
    (f : A ⟶ B) (g : B ⟶ A) (h : f ≫ g = 𝟙 A) (hgf : P (g ≫ f)) : P f :=
  P.of_retract (sectionRetract f g h) hgf

#print axioms sectionRetract
#print axioms property_section

end DaggerModels.PartII.SplitSectionArrowRetract
