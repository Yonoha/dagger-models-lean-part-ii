import DaggerModelsPartII.ProjectiveLocalEquivalences
import DaggerModelsPartII.LocalReplacementSolutionSet

/-!
# Smith recognition for projective local diagram equivalences

The exact boundary-generated projective cofibrations and the exact derived
local-equivalence class satisfy Smith recognition once a small solution set
for that class is supplied.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.ProjectiveKanDiagram

noncomputable section

variable (C : Type u) [Category.{u} C]

local instance localizationBaseModel : ModelCategory (C ⥤ SSet.{u}) := modelCategory C

/-- A solution set for the exact local class completes projective Smith recognition. -/
def localizationSmithData (S : MorphismProperty (C ⥤ SSet.{u}))
    (solution : DaggerSmithSolutionSet.SolutionData.{u}
      (boundaryGenerators C) (Localization.localEquivalences S)) :
    DaggerSmithSolutionSet.CombinatorialData solution := by
  letI := locallyPresentable C
  have hgen : (boundaryGenerators C).rlp.llp =
      HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}) := (model_cofibrations C).symm
  letI : ((boundaryGenerators C).rlp.llp ⊓
      Localization.localEquivalences S).IsStableUnderCobaseChange := by
    rw [hgen]
    exact localTrivialCofibrations_cobaseChange C S
  letI : IsStableUnderTransfiniteComposition.{u}
      ((boundaryGenerators C).rlp.llp ⊓ Localization.localEquivalences S) := by
    rw [hgen]
    exact localTrivialCofibrations_transfinite C S
  have hrlp : (boundaryGenerators C).rlp ≤ Localization.localEquivalences S := by
    intro A B f hf
    apply Localization.weakEquivalences_le_localEquivalences S f
    have htriv : HomotopicalAlgebra.trivialFibrations (C ⥤ SSet.{u}) f := by
      rw [← rlp_eq_of_wfs (HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}))
        (HomotopicalAlgebra.trivialFibrations (C ⥤ SSet.{u})),
        model_cofibrations C, rlp_llp_rlp]
      exact hf
    exact htriv.2
  exact DaggerSmithSolutionSet.combinatorialData solution hrlp

/-- Smith's constructed model has precisely the projective cofibrations and
the specified local weak equivalences. -/
theorem localizationSmith_exactClasses (S : MorphismProperty (C ⥤ SSet.{u}))
    (solution : DaggerSmithSolutionSet.SolutionData.{u}
      (boundaryGenerators C) (Localization.localEquivalences S)) :
    (localizationSmithData C S solution).model.categoryWithCofibrations.cofibrations =
      (modelCategory C).categoryWithCofibrations.cofibrations ∧
    (localizationSmithData C S solution).model.categoryWithWeakEquivalences.weakEquivalences =
      Localization.localEquivalences S := by
  exact ⟨(localizationSmithData C S solution).modelCof.trans (model_cofibrations C).symm,
    (localizationSmithData C S solution).modelWeak⟩

end

end DaggerModels.PartII.ProjectiveKanDiagram
