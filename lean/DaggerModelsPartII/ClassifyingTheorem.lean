import DaggerModelsPartII.LengthStageAttaching
import DaggerModelsPartII.LengthCellLocality
import DaggerModelsPartII.ClassifyingReduction

/-!
# The classifying proposition for the actual change-of-index unit

Actual cell-attachment pushouts and local trivial boundary inclusions make
all length-stage maps locally trivial. The verified reduction then applies
to the original adjunction unit, with no remaining stage hypothesis.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

namespace DaggerModels.PartII.ClassifyingTheorem

open SegalLocalizers LengthStageAttaching C2InvolutionActions
open LengthFiltrationColimit ActualIndexProjectiveModel

noncomputable section

private local instance : ModelCategory ReverseDaggerSpace.{0} := injectiveSegalModel

/-- Every successor stage of positive length is a local trivial cofibration. -/
theorem lengthStage_trivialCofibration (m ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    injectiveSegalModel.categoryWithCofibrations.cofibrations
        (discreteDiagram.map (stageInclusion m ℓ)) ∧
      injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
        (discreteDiagram.map (stageInclusion m ℓ)) := by
  have hp := lengthStage_discrete_isPushout m ℓ hℓ
  exact (trivialCofibrations ReverseDaggerSpace.{0}).of_isPushout hp
    (LengthCellLocality.boundaryToCell_localTrivial m ℓ hℓ)

/-- The first length stage includes into the full discrete native nerve
by a local trivial cofibration, without a remaining stage hypothesis. -/
theorem lengthOne_inclusion_trivial (m : ℕ) :
    injectiveSegalModel.categoryWithCofibrations.cofibrations
        (discreteDiagram.map (DaggerNerveLengthFiltration.lengthFiltration m 1).ι) ∧
      injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
        (discreteDiagram.map (DaggerNerveLengthFiltration.lengthFiltration m 1).ι) := by
  apply ClassifyingReduction.lengthOne_inclusion_trivial_of_successors m
  intro n
  exact lengthStage_trivialCofibration m (n + 2) (by omega)

/-- The original representable unit is a local trivial cofibration in the
manuscript's actual injective Segal localization. -/
theorem actualRepresentableUnit_trivial (m : ℕ) :
    injectiveSegalModel.categoryWithCofibrations.cofibrations
        ((actualLeftAdjunction.{0}).unit.app
          ((simplicialYoneda.{0, 0} DaggerModels.ReverseSimplex).obj
            (DaggerModels.ReverseSimplex.mk m))) ∧
      injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
        ((actualLeftAdjunction.{0}).unit.app
          ((simplicialYoneda.{0, 0} DaggerModels.ReverseSimplex).obj
            (DaggerModels.ReverseSimplex.mk m))) := by
  apply ClassifyingReduction.actualRepresentableUnit_trivial_of_successors m
  intro n
  exact lengthStage_trivialCofibration m (n + 2) (by omega)

end

end DaggerModels.PartII.ClassifyingTheorem
