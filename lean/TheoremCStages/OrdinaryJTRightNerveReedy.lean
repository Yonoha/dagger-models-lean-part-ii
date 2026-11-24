import OrdinaryJTMappingFunctor
import OrdinaryJTMappingFibration
import DaggerModelsPartII.StandardSimplexFrame

/-!
# Reedy fibrancy of the ordinary JT right-nerve Hom rows

The opposite standard simplex is Reedy fibrant in the original Joyal model.
The actual horizontal JT Hom functor preserves limits and takes its
fibrations to native Kan fibrations. Coefficient change therefore gives
Reedy fibrancy of the entire Hom-row diagram, not only its separate rows.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryJTRightNerveReedy

noncomputable section

private def ordinaryJoyalModel : ModelCategory SSet.{0} :=
  DaggerActualDCHRightInducedAndMainTheoremD.ordinaryJoyalModel.{0}

private def ordinaryOppositeModel : ModelCategory SSet.{0}ᵒᵖ := by
  letI : ModelCategory SSet.{0} := ordinaryJoyalModel
  exact inferInstance

private local instance : ModelCategory SSet.{0}ᵒᵖ := ordinaryOppositeModel
private local instance : CategoryWithFibrations SSet.{0}ᵒᵖ :=
  ordinaryOppositeModel.categoryWithFibrations
private local instance : ModelCategory (SimplexCategoryᵒᵖ ⥤ SSet.{0}ᵒᵖ) :=
  simplicialReedyModelCategory SSet.{0}ᵒᵖ
private local instance : ModelCategory (SimplexCategoryᵒᵖ ⥤ SSet.{0}) :=
  simplicialReedyModelCategory SSet.{0}

private theorem standardSimplex_op_original_reedyFibrant :
    IsFibrant SSet.stdSimplex.{0}.op := by
  apply (reedyFibrant_iff_matchingComparison _).mpr
  intro n
  apply ((fibrations SSet.{0}ᵒᵖ).cancel_right_of_respectsIso
    ((matchingComparison n).app SSet.stdSimplex.{0}.op)
    (matchingBoundaryIso.{0} n).hom).mp
  rw [matchingBoundaryIso_comp]
  change ordinaryJoyalModel.categoryWithCofibrations.cofibrations (SSet.boundary n).ι
  rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelCof,
    DaggerNativeFullWeakSmithGenerators.boundary_cof]
  change Mono (SSet.boundary n).ι
  infer_instance

/-- The entire unlifted JT right-nerve diagram, with its original Hom-row weights. -/
def plainSpace (X : SSet.{0}) : SimplexCategoryᵒᵖ ⥤ SSet.{0} :=
  SSet.stdSimplex.{0}.op ⋙ OrdinaryJTMappingFunctor.mappingFunctor X

/-- The full Hom-row ordinary JT right nerve is Reedy fibrant into a quasicategory. -/
theorem plainSpace_reedyFibrant (X : SSet.{0}) [X.Quasicategory] :
    IsFibrant (plainSpace X) := by
  letI : IsFibrant SSet.stdSimplex.{0}.op :=
    standardSimplex_op_original_reedyFibrant
  apply reedyFibrant_comp SSet.stdSimplex.{0}.op
    (OrdinaryJTMappingFunctor.mappingFunctor X)
  intro A B f hf
  have hm : Mono f.unop := by
    change ordinaryJoyalModel.categoryWithCofibrations.cofibrations f.unop at hf
    rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelCof,
      DaggerNativeFullWeakSmithGenerators.boundary_cof] at hf
    exact hf
  letI : Mono f.unop := hm
  change fibrations SSet.{0}
    (OrdinaryJTMappingFrameWeak.restriction X f.unop)
  exact (fibration_iff _).mp (OrdinaryJTMappingFibration.restriction_fibration X f.unop)

#print axioms plainSpace_reedyFibrant

end
end DaggerModels.PartII.OrdinaryJTRightNerveReedy
