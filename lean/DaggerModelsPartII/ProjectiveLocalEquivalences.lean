import DaggerModelsPartII.InjectiveLocalEquivalences
import DaggerModelsPartII.ProjectiveInjectiveComparison
import DaggerModelsPartII.KanLeftProper

/-!
# Projective local trivial cofibrations

The projective and injective diagram models define the same local weak
equivalences. We transfer transfinite stability of local trivial cofibrations
from the injective model, retaining the smaller projective cofibration class.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.ProjectiveKanDiagram

noncomputable section

variable (C : Type u) [Category.{u} C]

local instance localWeakProjectiveModel : ModelCategory (C ⥤ SSet.{u}) := modelCategory C

/-- Projective cofibrations that are local equivalences are stable under pushout. -/
theorem localTrivialCofibrations_cobaseChange (S : MorphismProperty (C ⥤ SSet.{u})) :
    (HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}) ⊓
      Localization.localEquivalences S).IsStableUnderCobaseChange := by
  letI : HasColimitsOfSize.{0, u} (C ⥤ SSet.{u}) := hasColimitsOfSizeShrink.{0, u} _
  exact Localization.localTrivialCofibrations_cobaseChange
    (fun sq hi hw ↦ model_leftProper C sq hi hw) S

/-- Projective cofibrations that are local equivalences are stable under
transfinite composition, for every localizing family. -/
theorem localTrivialCofibrations_transfinite (S : MorphismProperty (C ⥤ SSet.{u})) :
    IsStableUnderTransfiniteComposition.{u}
      (HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}) ⊓
        Localization.localEquivalences S) := by
  letI : IsStableUnderTransfiniteComposition.{u}
      (HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u})) := by
    rw [← llp_eq_of_wfs (HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}))
      (HomotopicalAlgebra.trivialFibrations (C ⥤ SSet.{u}))]
    infer_instance
  constructor
  intro J _ _ _ _
  constructor
  intro A B f hf
  refine ⟨(HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u})).transfiniteCompositionsOfShape_le J _
    (transfiniteCompositionsOfShape_monotone J inf_le_left _ hf), ?_⟩
  have hIncl :
      (HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}) ⊓
        Localization.localEquivalences S) ≤
      (letI := InjectiveKanDiagram.modelCategory C;
        HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}) ⊓
          Localization.localEquivalences S) := by
    intro X Y g hg
    refine ⟨ProjectiveInjectiveComparison.cofibrations_le C g hg.1, ?_⟩
    have heq := ProjectiveInjectiveComparison.localEquivalences_eq C S
    exact heq ▸ hg.2
  have hInjective := InjectiveKanDiagram.localTrivialCofibrations_transfinite C S
  have hMem :
      (letI := InjectiveKanDiagram.modelCategory C;
        HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}) ⊓
          Localization.localEquivalences S) f := by
    letI : ModelCategory (C ⥤ SSet.{u}) := InjectiveKanDiagram.modelCategory C
    letI : IsStableUnderTransfiniteComposition.{u}
        (HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}) ⊓
          Localization.localEquivalences S) := hInjective
    exact (HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}) ⊓
      Localization.localEquivalences S).transfiniteCompositionsOfShape_le J _
      (transfiniteCompositionsOfShape_monotone J hIncl _ hf)
  have heq := ProjectiveInjectiveComparison.localEquivalences_eq C S
  exact heq.symm ▸ hMem.2

end

end DaggerModels.PartII.ProjectiveKanDiagram
