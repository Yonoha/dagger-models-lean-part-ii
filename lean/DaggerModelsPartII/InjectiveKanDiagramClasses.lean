import DaggerModelsPartII.ProjectiveKanDiagram
import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory

/-! The cofibration and weak-equivalence classes for injective Kan diagrams. -/

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.InjectiveKanDiagram

variable (C : Type u) [Category.{u} C]

/-- The intended injective cofibrations are the levelwise monomorphisms. -/
def cofibrations : MorphismProperty (C ⥤ SSet.{u}) :=
  monomorphisms _

/-- The intended injective weak equivalences are the levelwise Kan weak equivalences. -/
abbrev weakEquivalences : MorphismProperty (C ⥤ SSet.{u}) :=
  ProjectiveKanDiagram.weakEquivalences C

/-- The intersection of the two intended classes. -/
def trivialCofibrations : MorphismProperty (C ⥤ SSet.{u}) :=
  cofibrations C ⊓ weakEquivalences C

/-- The intended trivial cofibrations are exactly the pointwise Kan trivial cofibrations. -/
theorem trivialCofibrations_eq :
    trivialCofibrations C =
      (HomotopicalAlgebra.trivialCofibrations SSet.{u}).functorCategory C := by
  rw [trivialCofibrations, cofibrations, ← functorCategory_monomorphisms (C := SSet.{u}) C,
    ← SSet.modelCategoryQuillen.cofibrations_eq]
  ext X Y f
  exact ⟨fun h c ↦ ⟨h.1 c, h.2 c⟩, fun h ↦ ⟨fun c ↦ (h c).1, fun c ↦ (h c).2⟩⟩

instance : (trivialCofibrations C).IsStableUnderCobaseChange := by
  rw [trivialCofibrations_eq]
  infer_instance

instance : (trivialCofibrations C).IsStableUnderRetracts := by
  rw [trivialCofibrations_eq]
  infer_instance

instance (J : Type u) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J] :
    (trivialCofibrations C).IsStableUnderTransfiniteCompositionOfShape J := by
  rw [trivialCofibrations_eq]
  infer_instance

end DaggerModels.PartII.InjectiveKanDiagram
