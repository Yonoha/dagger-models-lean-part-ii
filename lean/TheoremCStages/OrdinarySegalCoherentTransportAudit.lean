import OrdinaryGroupoidSimplexFullFaithfulnessAudit
import OrdinarySegalCoherentSourceTransport
import OrdinarySegalCoherentRightFixedTriangle

/-!
# Coherent source change at the unchanged original ordinary JT input

Both source objects are the actual original groupoid vertices of one
whole coherent arrow. The vertical fiber maps retain the original whole
map from the ordinary JT input. No raw-unit weakness, independent
homotopy-category recognition, completion, or Theorem C is asserted.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalCoherentTransportAudit

open OrdinaryCSSLocalization (Space)
open OrdinarySegalOrderedMappingMaps (mappingMap)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev E := GroupoidSimplex.parameter.obj ⦋1⦌
private abbrev input (W : SegalLocalizers.ReverseDaggerSpace.{0}) :=
  RawOrdinaryJTQuillenTranspose.input W

/-- The original ordinary JT input has the exact coherent source-change
invariance for every whole map into a Kan-injectively fibrant Segal target. -/
theorem originalInput_mappingMap_weak_iff
    (W : SegalLocalizers.ReverseDaggerSpace.{0})
    (hW : letI : ModelCategory SegalLocalizers.ReverseDaggerSpace.{0} :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hSegal : SegalLocalizers.segalCondition W)
    (V : Space) [IsFibrant V] (hV : OrdinaryCSSConditions.segalCondition V)
    (f : input W ⟶ V) (H : E ⟶ (input W).flip.obj (op ⦋0⦌))
    (y : ((input W).obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    WeakEquivalence (mappingMap f
      (SSet.yonedaEquiv (X := (input W).flip.obj (op ⦋0⦌)) (n := ⦋0⦌)
        (JTParameterContraction.parameterVertex ⦋1⦌ 0 ≫ H)) y) ↔
    WeakEquivalence (mappingMap f
      (SSet.yonedaEquiv (X := (input W).flip.obj (op ⦋0⦌)) (n := ⦋0⦌)
        (JTParameterContraction.parameterVertex ⦋1⦌ 1 ≫ H)) y) := by
  have : IsFibrant (input W) :=
    OrdinaryJTOrdinaryInputReedy.ordinaryInput_injectiveFibrant W hW
  exact OrdinarySegalCoherentSourceTransport.mappingMap_weak_iff_actual f
    (OrdinaryJTOrdinaryInputSegal.ordinaryInput_segalCondition W hSegal) hV H y

#print axioms originalInput_mappingMap_weak_iff
#print axioms OrdinarySegalCoherentSourceTransport.mappingMap_weak_iff
#print axioms OrdinarySegalCoherentFixedSpineIso.finalEdgeFiber_trivialFibration
#print axioms OrdinarySegalCoherentFixedTriangleSource.compositeToOriginalFiber_trivialFibration
#print axioms OrdinarySegalCoherentRightFixedTriangle.fixedTriangleProjection_trivialFibration
#print axioms WeakSpanMorphismTransfer.property_iff
#print axioms
  OrdinaryGroupoidSimplexFullFaithfulnessAudit.originalInput_constantGroupoidSimplex_mappingMap_weak
#print axioms JTTheoremCFromOriginalRawOrderedUnit.statement_of_originalRawOrderedUnit

end
end DaggerModels.PartII.OrdinarySegalCoherentTransportAudit
