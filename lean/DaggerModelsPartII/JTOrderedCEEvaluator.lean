import DaggerModelsPartII.JTOrderedFrameWeights
import DaggerModelsPartII.JTCylinderAugmentationWeak
import DaggerModelsPartII.JTConeLatchingMono

/-! Transfer the actual right-cone evaluation theorem to the original CE frame. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerModels DaggerSSetGluing

namespace DaggerModels.PartII.JTOrderedCEEvaluator

open JTOrderedFrameHomBar (evaluator evaluator_weak_iff)
open JTOrderedFrameWeights (ce_point_GW cone_point_GW standard_point_GW)

noncomputable section

private abbrev B := JTXiEndpointCollapse.boundary

section Joyal

private def joyalModel := DaggerActualDCHRightInducedAndMainTheoremD.ordinaryJoyalModel.{0}

local instance : ModelCategory SSet.{0} := joyalModel
local instance : CategoryWithFibrations SSet.{0} := joyalModel.categoryWithFibrations
local instance : ModelCategory (Under B) := JTEndpointCobase.underModel B

private theorem targetUnder_fibrant (X : SSet.{0}) [X.Quasicategory]
    (x y : X.obj (op ⦋0⦌)) :
    IsFibrant (JTConeMappingPresentation.targetUnder X x y) := by
  apply (UnderReedyCriterion.under_isFibrant_iff B _).mpr
  apply (isFibrant_iff_of_isTerminal (terminal.from X)
    (terminalIsTerminal : IsTerminal (⊤_ SSet.{0}))).mpr
  rw [fibration_iff]
  change DaggerNativeOriginalJoyalSmithModelData.modelData.model.categoryWithFibrations.fibrations
    (terminal.from X)
  rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelFib,
    DaggerNativeFullWeakSmithGenerators.boundary_cof]
  exact DaggerNativeJoyalWeakTrivialFibrationSpan.terminal_candidate X

end Joyal

open scoped SSet.modelCategoryQuillen

/-- The actual evaluation on the full weighted CE bar of an arbitrary
quasi-category at two specified ordered endpoints is Kan weak. -/
theorem evaluator_weak (X : SSet.{0}) [X.Quasicategory]
    (x y : X.obj (op ⦋0⦌)) :
    WeakEquivalence (evaluator
      (Under.lift JTXiEndpointCollapse.CE JTXiEndpointCollapse.CE_boundary)
      (JTConeMappingPresentation.targetUnder X x y)) := by
  let U := JTConeMappingPresentation.targetUnder X x y
  have hU := targetUnder_fibrant X x y
  have hCone : WeakEquivalence (JTCylinderMappingSpan.fromCone U) :=
    (weakEquivalence_iff_GW _).mpr
      (@JTCylinderMappingWeak.fromCone_GW U hU JTCylinderAugmentationWeak.augmentation_weak
        JTConeLatchingMono.coneUnder_op_isFibrant)
  have hCE : WeakEquivalence (JTCylinderMappingSpan.fromCE U) :=
    (weakEquivalence_iff_GW _).mpr
      (@JTCylinderMappingWeak.fromCE_GW U hU JTCylinderAugmentationWeak.augmentation_weak)
  have hCyl :=
    (evaluator_weak_iff U JTCylinderConeComparison.comparisonUnder hCone
      standard_point_GW cone_point_GW).mpr (JTOrderedConeEvaluator.evaluator_weak X x y)
  exact (evaluator_weak_iff U JTCylinderCEComparison.underComparison hCE
    standard_point_GW ce_point_GW).mp hCyl

end

end DaggerModels.PartII.JTOrderedCEEvaluator
