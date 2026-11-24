import DaggerModelsPartII.JTBoundaryNecklacePresentationCone

/-!
Transport a full assembled internal-necklace presentation through a natural
map of its cylinder diagram. The formula is proved with abstract diagrams,
before specializing any graph, coefficient family or fixed target.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTBoundaryNecklaceAssembleTransport

noncomputable section

private abbrev B := JTXiEndpointCollapse.boundary

variable {I A K : Type} [SmallCategory I] [SmallCategory A] [SmallCategory K]
variable (E : I ⥤ Under B) (C : A ⥤ Under B) (L : A ⥤ I)
variable (ρ : C ⟶ L ⋙ E) (b : K ⥤ A) (N : K ⥤ NecklaceCode)
variable (m : N ⋙ BoundaryNecklaceComma.necklaceUnder ⟶ b ⋙ C)

/-- Mapping the whole assembled presentation retains its original native
code and composes its exact complete traversal with the supplied lift. -/
theorem map_assemble :
    JTTargetCommaPullback.assemble C b N m ⋙
        JTBoundaryNecklacePresentationCone.mapPresentation E C L ρ =
      JTTargetCommaPullback.assemble E (b ⋙ L) N
        (m ≫ Functor.whiskerLeft b ρ) := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro a a' f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply JTTargetCommaPullback.operator_ext
  · rfl
  · change (BoundaryNecklaceComma.sourceCode E).map
        ((JTBoundaryNecklacePresentationCone.mapPresentation E C L ρ).map
          ((JTTargetCommaPullback.assemble C b N m).map f)) = N.map f
    exact JTBoundaryNecklacePresentationCone.mapPresentation_code E C L ρ
      ((JTTargetCommaPullback.assemble C b N m).map f)

end
end DaggerModels.PartII.JTBoundaryNecklaceAssembleTransport
