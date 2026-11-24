import DaggerModelsPartII.ActualUnitCornerGenerators
import DaggerModelsPartII.AdjunctionUnitInitial
import DaggerModelsPartII.UnitCornerClosure

/-!
# The actual unit on projectively cofibrant objects

The generator-corner theorem and the right-mate lifting equivalence extend
local triviality to every projective cofibration. Its initial-source case
is the literal original adjunction unit.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty DaggerModels

namespace DaggerModels.PartII.CofibrantUnit

open SegalLocalizers ActualIndexProjectiveModel AdjunctionUnitCorners

noncomputable section

private local instance : ModelCategory ReverseDaggerSpace.{0} := injectiveSegalModel

/-- The unit corner of any actual projective cofibration is locally trivial. -/
theorem actualUnitCorner_trivial_of_projectiveCofibration
    {X Y : ReverseDaggerSpace.{0}} (f : X ⟶ Y)
    (hf : (ProjectiveKanDiagram.modelCategory
      ReverseSimplexᵒᵖ).categoryWithCofibrations.cofibrations f) :
    injectiveSegalModel.categoryWithCofibrations.cofibrations
        (unitPushoutCorner (actualLeftAdjunction.{0}) f).ι ∧
      injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
        (unitPushoutCorner (actualLeftAdjunction.{0}) f).ι := by
  apply UnitCornerClosure.unitCorner_trivial_of_generators
    (actualLeftAdjunction.{0}) (actualRightAdjunction.{0})
    (ProjectiveKanDiagram.boundaryGenerators ReverseSimplexᵒᵖ) ?_ f ?_
  · intro A B i hi
    exact ActualUnitCornerGenerators.boundaryGenerators_unitCorner_trivial hi
  · exact hf

/-- For an initial-source projective cofibration the original unit itself
is a local trivial cofibration, with no generator hypothesis left over. -/
theorem actualUnit_trivial_of_initial_projectiveCofibration
    (X : ReverseDaggerSpace.{0})
    (hX : (ProjectiveKanDiagram.modelCategory
      ReverseSimplexᵒᵖ).categoryWithCofibrations.cofibrations (initial.to X)) :
    injectiveSegalModel.categoryWithCofibrations.cofibrations
        ((actualLeftAdjunction.{0}).unit.app X) ∧
      injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
        ((actualLeftAdjunction.{0}).unit.app X) := by
  have hc := actualUnitCorner_trivial_of_projectiveCofibration (initial.to X) hX
  let e := AdjunctionUnitInitial.unitPushoutCorner_initial_arrowIso
    (actualLeftAdjunction.{0}) (actualRightAdjunction.{0}) X
  exact ((trivialCofibrations ReverseDaggerSpace.{0}).arrow_mk_iso_iff e).mpr hc

/-- The original change-of-index unit is locally trivial on every
projectively cofibrant reversal diagram. -/
theorem actualUnit_trivial_of_projectiveCofibrant (X : ReverseDaggerSpace.{0})
    (hX : @IsCofibrant ReverseDaggerSpace.{0} _
      (ProjectiveKanDiagram.modelCategory
        ReverseSimplexᵒᵖ).categoryWithCofibrations _ X) :
    injectiveSegalModel.categoryWithCofibrations.cofibrations
        ((actualLeftAdjunction.{0}).unit.app X) ∧
      injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
        ((actualLeftAdjunction.{0}).unit.app X) := by
  have hc : (ProjectiveKanDiagram.modelCategory
      ReverseSimplexᵒᵖ).categoryWithCofibrations.cofibrations (initial.to X) := by
    letI : CategoryWithCofibrations ReverseDaggerSpace.{0} :=
      (ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ).categoryWithCofibrations
    exact (cofibration_iff (initial.to X)).mp hX
  exact actualUnit_trivial_of_initial_projectiveCofibration X hc

/-- The same unit theorem for cofibrancy in the localized projective
model; localization has the identical projective cofibration class. -/
theorem actualUnit_trivial_of_localizedProjectiveCofibrant
    (X : ReverseDaggerSpace.{0})
    (hX : @IsCofibrant ReverseDaggerSpace.{0} _
      projectiveSegalModel.categoryWithCofibrations _ X) :
    injectiveSegalModel.categoryWithCofibrations.cofibrations
        ((actualLeftAdjunction.{0}).unit.app X) ∧
      injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
        ((actualLeftAdjunction.{0}).unit.app X) := by
  have hc : projectiveSegalModel.categoryWithCofibrations.cofibrations
      (initial.to X) := by
    letI : CategoryWithCofibrations ReverseDaggerSpace.{0} :=
      projectiveSegalModel.categoryWithCofibrations
    exact (cofibration_iff (initial.to X)).mp hX
  change (ProjectiveKanDiagram.localizedModelCategory ReverseSimplexᵒᵖ
    LocalizerIndex localizerArrow localizerArrow_mono).categoryWithCofibrations.cofibrations
      (initial.to X) at hc
  rw [(ProjectiveKanDiagram.localized_exactClasses ReverseSimplexᵒᵖ
    LocalizerIndex localizerArrow localizerArrow_mono).1] at hc
  exact actualUnit_trivial_of_initial_projectiveCofibration X hc

end

end DaggerModels.PartII.CofibrantUnit
