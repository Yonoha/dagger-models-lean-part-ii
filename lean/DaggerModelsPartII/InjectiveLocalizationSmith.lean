import DaggerModelsPartII.InjectiveLocalEquivalences
import DaggerModelsPartII.LocalReplacementSolutionSet

/-! Smith recognition for the exact injective local-equivalence class. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.InjectiveKanDiagram

noncomputable section

variable (C : Type u) [Category.{u} C]

local instance localizationBaseModel : ModelCategory (C ⥤ SSet.{u}) := modelCategory C

/-- A small solution set for the exact local class completes injective Smith recognition. -/
def localizationSmithData (S : MorphismProperty (C ⥤ SSet.{u}))
    (solution : DaggerSmithSolutionSet.SolutionData.{u}
      (quotientSubobjectGenerators C) (Localization.localEquivalences S)) :
    DaggerSmithSolutionSet.CombinatorialData solution := by
  letI := ProjectiveKanDiagram.locallyPresentable C
  have hgen : (quotientSubobjectGenerators C).rlp.llp =
      HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}) := by
    rw [model_cofibrations C]
    exact quotientGeneratedCofibrations_eq_cofibrations C
  letI : ((quotientSubobjectGenerators C).rlp.llp ⊓
      Localization.localEquivalences S).IsStableUnderCobaseChange := by
    rw [hgen]
    exact localTrivialCofibrations_cobaseChange C S
  letI : IsStableUnderTransfiniteComposition.{u}
      ((quotientSubobjectGenerators C).rlp.llp ⊓ Localization.localEquivalences S) := by
    rw [hgen]
    exact localTrivialCofibrations_transfinite C S
  have hrlp : (quotientSubobjectGenerators C).rlp ≤ Localization.localEquivalences S := by
    intro A B f hf
    apply Localization.weakEquivalences_le_localEquivalences S f
    rw [model_weakEquivalences C]
    exact generators_rlp_le_weak C (generatorsAreAllMonos C) f hf
  exact DaggerSmithSolutionSet.combinatorialData solution hrlp

end

end DaggerModels.PartII.InjectiveKanDiagram
