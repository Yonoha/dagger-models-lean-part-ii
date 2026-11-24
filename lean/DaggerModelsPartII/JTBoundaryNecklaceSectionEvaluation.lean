import DaggerModelsPartII.JTBoundaryNecklaceAssembleTransport

/-!
Evaluate a complete assembled section by an abstract cylinder-diagram map.
The identity-index simplification is proved before any concrete graph family,
so specializations need only identify their full traversal natural transformation.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTBoundaryNecklaceSectionEvaluation

noncomputable section

private abbrev B := JTXiEndpointCollapse.boundary

variable {I A X : Type} [SmallCategory I] [SmallCategory A] [SmallCategory X]
variable (E : I ⥤ Under B) (C : A ⥤ Under B) (L : A ⥤ I)
variable (ρ : C ⟶ L ⋙ E) (N : A ⥤ NecklaceCode)
variable (m : N ⋙ BoundaryNecklaceComma.necklaceUnder ⟶ C)
variable (H : BoundaryNecklaceComma.Presentation E ⥤ X)

/-- The full section evaluates by exactly its original code and paired traversal. -/
theorem evaluate_section :
    JTTargetCommaPullback.assemble C (𝟭 A) N m ⋙
        (JTBoundaryNecklacePresentationCone.mapPresentation E C L ρ ⋙ H) =
      JTTargetCommaPullback.assemble E L N (m ≫ ρ) ⋙ H := by
  rw [← Functor.assoc, JTBoundaryNecklaceAssembleTransport.map_assemble]
  rfl

/-- Any proved equality of complete paired traversals transports the exact
section evaluation, including every native operator and internal necklace. -/
theorem evaluate_section_of_eq
    (s : N ⋙ BoundaryNecklaceComma.necklaceUnder ⟶ L ⋙ E) (h : m ≫ ρ = s) :
    JTTargetCommaPullback.assemble C (𝟭 A) N m ⋙
        (JTBoundaryNecklacePresentationCone.mapPresentation E C L ρ ⋙ H) =
      JTTargetCommaPullback.assemble E L N s ⋙ H := by
  rw [evaluate_section, h]

end
end DaggerModels.PartII.JTBoundaryNecklaceSectionEvaluation
