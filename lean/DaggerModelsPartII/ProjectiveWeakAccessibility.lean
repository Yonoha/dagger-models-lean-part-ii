import DaggerModelsPartII.ModelWeakAccessibility
import DaggerModelsPartII.ProjectiveKanDiagram

/-! Accessibility and small solution sets for the literal levelwise Kan weak equivalences. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.ProjectiveKanDiagram

noncomputable section

variable (C : Type u) [Category.{u} C]

local instance : ModelCategory (C ⥤ SSet.{u}) := modelCategory C
local instance : IsLocallyPresentable.{u} (C ⥤ SSet.{u}) := locallyPresentable C

private theorem boundaryGenerators_model_rlp :
    (boundaryGenerators C).rlp = HomotopicalAlgebra.trivialFibrations (C ⥤ SSet.{u}) := by
  rw [boundaryGenerators_rlp, ← fibrations_inf_weakEquivalences]
  rfl

private theorem hornGenerators_model_rlp :
    (hornGenerators C).rlp = HomotopicalAlgebra.fibrations (C ⥤ SSet.{u}) :=
  hornGenerators_rlp C

/-- The full subcategory of levelwise Kan weak-equivalence arrows is accessible. -/
theorem weakArrow_isAccessible :
    IsAccessibleCategory.{u}
      (DaggerAccessibleSolutions.arrowProperty (weakEquivalences C)).FullSubcategory :=
  ModelWeakAccessibility.weakArrow_isAccessible (boundaryGenerators C) (hornGenerators C)
    (boundaryGenerators_model_rlp C) (hornGenerators_model_rlp C)

/-- Its inclusion into all diagram arrows is accessible. -/
theorem weakArrow_inclusion_isAccessible :
    Functor.IsAccessible.{u} (DaggerAccessibleSolutions.arrowProperty (weakEquivalences C)).ι :=
  ModelWeakAccessibility.weakArrow_inclusion_isAccessible (boundaryGenerators C) (hornGenerators C)
    (boundaryGenerators_model_rlp C) (hornGenerators_model_rlp C)

/-- Every small family has a Smith solution set against the exact levelwise weak class. -/
def weakSolutionSet (K : MorphismProperty (C ⥤ SSet.{u})) [IsSmall.{u} K] :
    DaggerSmithSolutionSet.SolutionData.{u} K (weakEquivalences C) := by
  let W := DaggerAccessibleSolutions.arrowProperty (weakEquivalences C)
  letI := DaggerRLPAccessibility.arrowLocallyPresentable (C ⥤ SSet.{u})
  letI : IsAccessibleCategory.{u} W.FullSubcategory := weakArrow_isAccessible C
  letI : Functor.IsAccessible.{u} W.ι := weakArrow_inclusion_isAccessible C
  exact DaggerAccessibleSolutions.ofAccessible K (weakEquivalences C)

end

end DaggerModels.PartII.ProjectiveKanDiagram
