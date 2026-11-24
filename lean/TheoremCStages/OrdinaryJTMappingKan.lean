import DaggerModelsPartII.JTOrdinaryEndpointFibration
import StrictFrameMappingKan
import OrdinaryJTMappingFrameWeak

/-!
# Kan rows of the ordinary JT right nerve

Every row `Hom(A × J[•], X)` is Kan for an ordinary quasicategory `X`.
The proof applies the absolute strict-frame result to the same checked
ordinary JT parameter; no relative spine-corner calculation is needed.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open MonoidalCategory DaggerModels

namespace DaggerModels.PartII.OrdinaryJTMappingKan

noncomputable section

open OrdinaryJTMappingFrameWeak

private def ordinaryJoyalModel : ModelCategory SSet.{0} :=
  DaggerActualDCHRightInducedAndMainTheoremD.ordinaryJoyalModel.{0}

private local instance : ModelCategory SSet.{0} := ordinaryJoyalModel
private local instance : CategoryWithWeakEquivalences SSet.{0} :=
  ordinaryJoyalModel.categoryWithWeakEquivalences
private local instance : ModelCategory SSet.{0}ᵒᵖ := inferInstance
private local instance : CategoryWithWeakEquivalences SSet.{0}ᵒᵖ :=
  (inferInstance : ModelCategory SSet.{0}ᵒᵖ).categoryWithWeakEquivalences
private local instance : ModelCategory (SimplexCategoryᵒᵖ ⥤ SSet.{0}ᵒᵖ) :=
  simplicialReedyModelCategory SSet.{0}ᵒᵖ

private theorem isFibrant_of_quasicategory (X : SSet.{0})
    [X.Quasicategory] : IsFibrant X := by
  apply (isFibrant_iff_of_isTerminal (terminal.from X)
    (terminalIsTerminal : IsTerminal (⊤_ SSet.{0}))).mpr
  rw [fibration_iff]
  change ordinaryJoyalModel.categoryWithFibrations.fibrations (terminal.from X)
  rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelFib,
    DaggerNativeFullWeakSmithGenerators.boundary_cof]
  exact DaggerNativeJoyalWeakTrivialFibrationSpan.terminal_candidate X

/-- All literal ordinary JT mapping rows into a quasicategory are Kan. -/
theorem mapping_kan (X A : SSet.{0}) [X.Quasicategory] :
    (mapping X A).KanComplex := by
  letI : IsFibrant X := isFibrant_of_quasicategory X
  letI : IsFibrant (frame A).op := frame_op_isFibrant A
  have hframe : ∀ {s t : SimplexCategoryᵒᵖ} (g : s ⟶ t),
      weakEquivalences SSet.{0}ᵒᵖ ((frame A).op.map g) := by
    intro s t g
    rw [weakEquivalences_op]
    change ordinaryJoyalModel.categoryWithWeakEquivalences.weakEquivalences
      (A ◁ GroupoidSimplex.parameter.map g.unop)
    rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelWeak]
    exact DaggerNativeJoyalMappingTensor.weak_whiskerLeft A
      (GroupoidSimplex.parameter.map g.unop)
      (JTOrdinaryEndpointFibration.parameter_map_weak g.unop)
  exact StrictFrameMappingKan.strictMapping_obj_isFibrant X (frame A).op hframe

#print axioms mapping_kan

end

end DaggerModels.PartII.OrdinaryJTMappingKan
