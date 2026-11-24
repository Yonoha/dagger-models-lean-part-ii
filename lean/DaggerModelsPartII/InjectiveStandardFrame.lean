import DaggerModelsPartII.StandardSimplexFrame
import DaggerModelsPartII.InjectiveDerivedMapping
import Mathlib.CategoryTheory.Limits.Preserves.Opposites

/-! The standard simplex tensor is a Reedy fibrant frame in the injective model. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite Simplicial
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.InjectiveKanDiagram

variable (C : Type u) [Category.{u} C] [hgen : Fact (GeneratorsAreAllMonos C)]

noncomputable section

local instance standardInjectiveModel : ModelCategory (C ⥤ SSet.{u}) :=
  modelOfGeneratorDensity C hgen.out

local instance standardFrameModel : ModelCategory (SimplexCategoryᵒᵖ ⥤ (C ⥤ SSet.{u})ᵒᵖ) :=
  simplicialReedyModelCategory (C ⥤ SSet.{u})ᵒᵖ

local instance standardSimplexFrameModel : ModelCategory
    (SimplexCategoryᵒᵖ ⥤ SSet.{u}ᵒᵖ) :=
  simplicialReedyModelCategory SSet.{u}ᵒᵖ

/-- The standard tensor frame is Reedy fibrant in the opposite injective model. -/
theorem standardFrame_reedyFibrant (A : C ⥤ SSet.{u}) :
    IsFibrant (standardFrame C A) := by
  letI : IsFibrant SSet.stdSimplex.{u}.op := standardSimplex_op_reedyFibrant
  letI : PreservesColimitsOfSize.{0, 0} (diagramTensor A) :=
    (diagramTensorMappingAdjunction A).leftAdjoint_preservesColimits
  letI : PreservesLimitsOfSize.{0, 0} (diagramTensor A).op :=
    preservesLimitsOfSize_op (diagramTensor A)
  change IsFibrant (SSet.stdSimplex.{u}.op ⋙ (diagramTensor A).op)
  apply reedyFibrant_comp SSet.stdSimplex.{u}.op (diagramTensor A).op
  intro X Y f hf
  rw [fibrations_op] at hf ⊢
  exact ((diagramTensor A).preservesCofibrations_iff.mp
    (diagramTensor_preservesCofibrations C A)) f.unop hf

/-- In the injective model, the strict mapping-space weak-equivalence test
agrees with the chosen derived mapping-space test for every source map. -/
theorem homotopyMappingWeakEquivalences_iff_strict
    {A B W : C ⥤ SSet.{u}} [IsFibrant W] (f : A ⟶ B) :
    homotopyMappingWeakEquivalences W f ↔
      HomotopicalAlgebra.weakEquivalences SSet.{u} (diagramMappingPrecomp f W) :=
  homotopyMappingWeakEquivalences_iff_strict_of_reedyFibrant C f
    (standardFrame_reedyFibrant C A) (standardFrame_reedyFibrant C B)

end

end DaggerModels.PartII.InjectiveKanDiagram
