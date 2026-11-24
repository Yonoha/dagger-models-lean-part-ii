import OrdinarySegalCotensorFoundationsAudit
import OrdinarySegalConstantWalkingFullyFaithful
import OrdinarySegalCotensorUnitMappingDiagonal

/-!
# Walking full faithfulness at the original raw JT input

The original ordinary input is Kan-injectively fibrant and Segal under
the original hypotheses. The literal constant walking section therefore
acts weakly on its actual ordered mapping fibers. This does not identify
that section with the original raw transpose or prove Theorem C.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalWalkingFullFaithfulnessAudit

noncomputable section

private local instance : ModelCategory OrdinaryCSSLocalization.Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev J := GroupoidSimplex.parameter.obj ⦋1⦌

/-- The same exact constant walking section is weak on every ordered
mapping fiber of the original ordinary JT input, without completeness. -/
theorem originalInput_constantWalking_mappingMap_weak
    (W : SegalLocalizers.ReverseDaggerSpace.{0})
    (hW : letI : ModelCategory SegalLocalizers.ReverseDaggerSpace.{0} :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hSegal : SegalLocalizers.segalCondition W)
    (x y : ((RawOrdinaryJTQuillenTranspose.input W).obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    WeakEquivalence (OrdinarySegalOrderedMappingMaps.mappingMap
      (OrdinarySegalHorizontalCotensorPoint.constantSection J
        (RawOrdinaryJTQuillenTranspose.input W)) x y) := by
  have : IsFibrant (RawOrdinaryJTQuillenTranspose.input W) :=
    OrdinaryJTOrdinaryInputReedy.ordinaryInput_injectiveFibrant W hW
  exact OrdinarySegalConstantWalkingFullyFaithful.mappingMap_weak
    (RawOrdinaryJTQuillenTranspose.input W)
    (OrdinaryJTOrdinaryInputSegal.ordinaryInput_segalCondition W hSegal) x y

#print axioms originalInput_constantWalking_mappingMap_weak
#print axioms OrdinarySegalCotensorSimplexCalibration.mappingIso_simplex_hom
#print axioms OrdinarySegalCotensorRelativeEndpointFibration.relativeEndpoint_fibration
#print axioms OrdinarySegalCotensorOrderedMappingFibration.mappingMap_fibration
#print axioms KanHomotopyMonomorphismFibre.pairedBase_fibration
#print axioms KanHomotopyMonomorphismFibreCalibration.exactFibreMap_diagonal_weak
#print axioms KanHomotopyMonomorphismSpecifiedFibre.fibreMap_diagonal_weak
#print axioms OrdinarySegalCotensorUnitMappingDiagonal.unit_mappingMap_diagonal_weak
#print axioms OrdinarySegalConstantWalkingFullyFaithful.mappingMap_weak
#print axioms JTTheoremCFromOriginalRawOrderedUnit.statement_of_originalRawOrderedUnit

end
end DaggerModels.PartII.OrdinarySegalWalkingFullFaithfulnessAudit
