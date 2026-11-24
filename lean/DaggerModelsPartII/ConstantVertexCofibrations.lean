import DaggerModelsPartII.ConstantVertexAdjunction
import DaggerModelsPartII.SegalLocalizationModels
import OriginalActualDaggerModelConstruction

/-!
# Cofibrations under the constant-vertex functor

The constant-vertex functor carries free dagger cofibrations to monomorphisms
of reversal simplicial spaces. This identifies its image with cofibrations in
the exact injective Segal localization; no weak-equivalence claim is made here.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra MorphismProperty DaggerModels

namespace DaggerModels.PartII.ConstantVertexAdjunction

noncomputable section

/-- The constant-vertex functor preserves cofibrations for the original
dagger Joyal and the injective Segal model structures. -/
theorem delta_map_cofibration {X Y : DaggerSSet.{0}} (f : X ⟶ Y)
    (hf : DaggerOriginalJoyalModel.standardModelCategory.categoryWithCofibrations.cofibrations
      f) :
    SegalLocalizers.injectiveSegalModel.categoryWithCofibrations.cofibrations
      (delta.map f) := by
  have hfree : DaggerSSet.freeCofibrations f := by
    rw [DaggerOriginalJoyalModel.standard_model_cof] at hf
    exact hf
  letI : Mono f := hfree.1
  have hmono : Mono (delta.map f) :=
    SegalLocalizers.discreteDagger_map_mono f
  rw [show SegalLocalizers.injectiveSegalModel.categoryWithCofibrations.cofibrations =
      (InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ).categoryWithCofibrations.cofibrations
      from
        (InjectiveKanDiagram.localized_exactClasses ReverseSimplexᵒᵖ
          SegalLocalizers.LocalizerIndex SegalLocalizers.localizerArrow
          SegalLocalizers.localizerArrow_mono).1]
  have hcof :
      (InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ).categoryWithCofibrations.cofibrations =
        monomorphisms _ := by
    letI : ModelCategory SegalLocalizers.ReverseDaggerSpace.{0} :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
    exact InjectiveKanDiagram.model_cofibrations ReverseSimplexᵒᵖ
  rw [hcof]
  exact hmono

end

end DaggerModels.PartII.ConstantVertexAdjunction
