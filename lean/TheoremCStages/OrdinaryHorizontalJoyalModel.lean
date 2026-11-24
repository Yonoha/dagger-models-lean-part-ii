import OrdinarySpaceReedyInjective
import OrdinaryJTProjectiveQuillen
import OriginalEquivalenceModelTransport
import Mathlib.AlgebraicTopology.ModelCategory.Opposite
import Mathlib.CategoryTheory.Functor.Currying

/-!
# Horizontal Joyal Reedy model on ordinary simplicial spaces

The same original bisimplicial presheaf is flipped before applying the
Reedy model with the original ordinary Joyal coefficient model. This
retains every horizontal row and every operator. The two-opposite
category is used only to keep the transported model classes distinct
while constructing two model structures on the same category.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryHorizontalJoyalModel

noncomputable section

abbrev Space := SimplexCategoryᵒᵖ ⥤ SSet.{0}

private abbrev J := OrdinaryJTProjectiveQuillen.joyalModel

private def verticalJoyalModel : ModelCategory Space := by
  letI : ModelCategory SSet.{0} := J
  letI : CategoryWithCofibrations SSet.{0} := J.categoryWithCofibrations
  letI : CategoryWithFibrations SSet.{0} := J.categoryWithFibrations
  letI : CategoryWithWeakEquivalences SSet.{0} := J.categoryWithWeakEquivalences
  exact simplicialReedyModelCategory SSet.{0}

private def doubledModel : ModelCategory Spaceᵒᵖᵒᵖ := by
  letI : ModelCategory Space := verticalJoyalModel
  letI : CategoryWithCofibrations Space := verticalJoyalModel.categoryWithCofibrations
  letI : CategoryWithFibrations Space := verticalJoyalModel.categoryWithFibrations
  letI : CategoryWithWeakEquivalences Space :=
    verticalJoyalModel.categoryWithWeakEquivalences
  letI : ModelCategory Spaceᵒᵖ := inferInstance
  exact inferInstance

/-- Flip the two original simplicial indices, then retain the result in
a separate but canonically equivalent category. -/
def flipDouble : Space ≌ Spaceᵒᵖᵒᵖ :=
  (Functor.flipping : Space ≌ Space).trans (opOpEquivalence Space).symm

def horizontalWeak : MorphismProperty Space :=
  doubledModel.categoryWithWeakEquivalences.weakEquivalences.inverseImage
    flipDouble.functor

def horizontalCof : MorphismProperty Space :=
  doubledModel.categoryWithCofibrations.cofibrations.inverseImage
    flipDouble.functor

def horizontalFib : MorphismProperty Space :=
  doubledModel.categoryWithFibrations.fibrations.inverseImage
    flipDouble.functor

/-- The horizontal Reedy model with literal ordinary Joyal weak maps in
every flipped row. -/
def model : ModelCategory Space := by
  letI : CategoryWithWeakEquivalences Space := ⟨horizontalWeak⟩
  letI : CategoryWithCofibrations Space := ⟨horizontalCof⟩
  letI : CategoryWithFibrations Space := ⟨horizontalFib⟩
  letI : ModelCategory Spaceᵒᵖᵒᵖ := doubledModel
  letI : CategoryWithWeakEquivalences Spaceᵒᵖᵒᵖ :=
    doubledModel.categoryWithWeakEquivalences
  letI : CategoryWithCofibrations Spaceᵒᵖᵒᵖ :=
    doubledModel.categoryWithCofibrations
  letI : CategoryWithFibrations Spaceᵒᵖᵒᵖ :=
    doubledModel.categoryWithFibrations
  exact DaggerOriginalEquivalenceModelTransport.transportModel flipDouble rfl rfl rfl

/-- Horizontal weakness is ordinary Joyal weakness on every original
fixed-vertical row. -/
theorem weak_iff_rows {W V : Space} (f : W ⟶ V) :
    model.categoryWithWeakEquivalences.weakEquivalences f ↔
      ∀ k : SimplexCategory,
        J.categoryWithWeakEquivalences.weakEquivalences
          (((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type 0)).map f).app
            (op k)) := by
  change horizontalWeak f ↔ _
  change (∀ q : SimplexCategoryᵒᵖ,
      J.categoryWithWeakEquivalences.weakEquivalences
        (((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type 0)).map f).app q)) ↔ _
  constructor
  · intro h k
    exact h (op k)
  · intro h q
    exact h q.unop

private theorem joyal_cof_eq_mono :
    J.categoryWithCofibrations.cofibrations = monomorphisms SSet.{0} := by
  let M : ModelCategory SSet.{0} :=
    DaggerNativeOriginalJoyalSmithModelData.modelData.model
  change M.categoryWithCofibrations.cofibrations = monomorphisms SSet.{0}
  rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelCof]
  exact DaggerNativeFullWeakSmithGenerators.boundary_cof

private theorem vertical_cof_eq_mono :
    verticalJoyalModel.categoryWithCofibrations.cofibrations =
      monomorphisms Space := by
  have hkan := OrdinarySpaceReedyInjective.reedy_cofibrations_eq_monomorphisms
  change reedyLatchingProperty (cofibrations SSet.{0}) = monomorphisms Space at hkan
  rw [SSet.modelCategoryQuillen.cofibrations_eq] at hkan
  change reedyLatchingProperty J.categoryWithCofibrations.cofibrations =
    monomorphisms Space
  rw [joyal_cof_eq_mono]
  exact hkan

/-- The original horizontal Joyal Reedy cofibrations are exactly all
monomorphisms of ordinary simplicial spaces. -/
theorem cofibrations_eq_monomorphisms :
    model.categoryWithCofibrations.cofibrations = monomorphisms Space := by
  ext W V f
  change horizontalCof f ↔ Mono f
  change (verticalJoyalModel.categoryWithCofibrations.cofibrations
    ((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type 0)).map f)) ↔ Mono f
  rw [vertical_cof_eq_mono]
  exact (Functor.flipping : Space ≌ Space).functor.mono_map_iff_mono f

#print axioms model
#print axioms weak_iff_rows
#print axioms cofibrations_eq_monomorphisms

end
end DaggerModels.PartII.OrdinaryHorizontalJoyalModel
