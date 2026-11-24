import OrdinaryCSSHorizontalJoyalFibrancy
import OrdinaryCSSConditions
import DaggerModelsPartII.MappingChangeModel

/-!
# Horizontal Joyal weak equivalences are actual CSS weak equivalences

The horizontal Joyal model and the injective Kan base have the same literal
monomorphism cofibrations. A CSS-local target is fibrant for both models.
The checked change-of-model mapping theorem therefore transfers each
horizontal weak equivalence to every exact CSS local mapping test.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryCSSHorizontalWeak

open OrdinaryCSSLocalization (Space)

noncomputable section

private abbrev H := OrdinaryHorizontalJoyalModel.model
private abbrev N := InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ
private local instance : ModelCategory Space := N

private theorem cofibrations_eq :
    H.categoryWithCofibrations.cofibrations = N.categoryWithCofibrations.cofibrations := by
  rw [OrdinaryHorizontalJoyalModel.cofibrations_eq_monomorphisms]
  exact (InjectiveKanDiagram.model_cofibrations SimplexCategoryᵒᵖ).symm

/-- Every actual horizontal Joyal Reedy weak equivalence is weak in the
fixed ordinary CSS localization of the injective Kan model. -/
theorem horizontal_weak_le_css :
    H.categoryWithWeakEquivalences.weakEquivalences ≤
      OrdinaryCSSLocalization.model.categoryWithWeakEquivalences.weakEquivalences := by
  intro X Y f hf
  rw [OrdinaryCSSLocalization.exactClasses.2]
  intro W hW
  have hCSS := (OrdinaryCSSLocalization.isFibrant_iff W).mpr hW
  have hH := OrdinaryCSSHorizontalJoyalFibrancy.horizontal_isFibrant W hCSS
  have hN := hW.1
  have htest : @homotopyMappingWeakEquivalences Space _ H _ _ W _ _ f := by
    letI : ModelCategory Space := H
    letI : IsFibrant W := hH
    exact weakEquivalences_le_homotopyMappingWeakEquivalences W f hf
  exact (homotopyMappingWeakEquivalences_iff_of_cofibrations_eq
    H N cofibrations_eq W hH hN f).mp htest

/-- Literal Joyal weakness on every original horizontal row suffices for
the actual CSS weak class, with no fibrancy hypothesis on either endpoint. -/
theorem weak_of_rows {W V : Space} (f : W ⟶ V)
    (hf : ∀ k : SimplexCategory,
      OrdinaryJTProjectiveQuillen.joyalModel.categoryWithWeakEquivalences.weakEquivalences
        (((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type 0)).map f).app
          (Opposite.op k))) :
    OrdinaryCSSLocalization.model.categoryWithWeakEquivalences.weakEquivalences f :=
  horizontal_weak_le_css f ((OrdinaryHorizontalJoyalModel.weak_iff_rows f).mpr hf)

#print axioms horizontal_weak_le_css
#print axioms weak_of_rows

end
end DaggerModels.PartII.OrdinaryCSSHorizontalWeak
