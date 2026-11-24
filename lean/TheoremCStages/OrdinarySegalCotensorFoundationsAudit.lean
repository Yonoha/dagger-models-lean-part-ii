import OrdinarySegalCoherentEvaluationAudit
import OrdinarySegalCotensorUnitHomotopyMono
import OrdinaryIntervalPrismTwoTriangleSquare
import OrdinarySegalUnitMiddleFibrations
import KanHomotopyMonomorphismCancellation
import OrdinarySegalCotensorEndpointCorner
import OrdinarySegalCotensorEndpointCalibration
import OrdinarySegalConstantIntervalFullyFaithful

/-!
# Cotensor foundations at the original reverse-dagger input

This audit applies the cotensor Segal theorem and the weak-diagonal theorem
to the unchanged ordinary input of the raw JT transpose. The original
ordered raw-unit fiber weakness, Segal completion, and Theorem C remain
separate unproved obligations.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalCotensorFoundationsAudit

noncomputable section

private local instance : ModelCategory OrdinaryCSSLocalization.Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- Every exact horizontal cotensor of the original ordinary input has
the original spine Segal condition, without ordinary completeness. -/
theorem originalInput_cotensor_segalCondition (K : SSet.{0})
    (W : SegalLocalizers.ReverseDaggerSpace.{0})
    (hW : letI : ModelCategory SegalLocalizers.ReverseDaggerSpace.{0} :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hSegal : SegalLocalizers.segalCondition W) :
    OrdinaryCSSConditions.segalCondition
      (OrdinarySegalHorizontalCotensor.cotensor K (RawOrdinaryJTQuillenTranspose.input W)) := by
  have : IsFibrant (RawOrdinaryJTQuillenTranspose.input W) :=
    OrdinaryJTOrdinaryInputReedy.ordinaryInput_injectiveFibrant W hW
  exact OrdinarySegalCotensorSegal.cotensor_segalCondition K _
    (OrdinaryJTOrdinaryInputSegal.ordinaryInput_segalCondition W hSegal)

/-- At the same input, the literal walking-unit restriction in every
horizontal row has weak strict diagonal. -/
theorem originalInput_unitRow_diagonal_weak
    (W : SegalLocalizers.ReverseDaggerSpace.{0})
    (hW : letI : ModelCategory SegalLocalizers.ReverseDaggerSpace.{0} :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hSegal : SegalLocalizers.segalCondition W) (n : SimplexCategory) :
    WeakEquivalence (KanHomotopyMonomorphism.diagonal
      ((OrdinarySegalHorizontalCotensor.pre
        (JTCylinderCEComparison.simplexUnit.app ⦋1⦌)
        (RawOrdinaryJTQuillenTranspose.input W)).app (op n))) := by
  have : IsFibrant (RawOrdinaryJTQuillenTranspose.input W) :=
    OrdinaryJTOrdinaryInputReedy.ordinaryInput_injectiveFibrant W hW
  exact OrdinarySegalCotensorUnitHomotopyMono.unitRow_diagonal_weak
    (RawOrdinaryJTQuillenTranspose.input W)
    (OrdinaryJTOrdinaryInputSegal.ordinaryInput_segalCondition W hSegal) n

/-- The constant interval section is weak on the exact ordinary input's
ordered fibers. This is not the still-unproved original raw-unit fiber map. -/
theorem originalInput_constantInterval_mappingMap_weak
    (W : SegalLocalizers.ReverseDaggerSpace.{0})
    (hW : letI : ModelCategory SegalLocalizers.ReverseDaggerSpace.{0} :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hSegal : SegalLocalizers.segalCondition W)
    (x y : ((RawOrdinaryJTQuillenTranspose.input W).obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    WeakEquivalence (OrdinarySegalOrderedMappingMaps.mappingMap
      (OrdinarySegalHorizontalCotensorPoint.constantSection (Δ[1] : SSet.{0})
        (RawOrdinaryJTQuillenTranspose.input W)) x y) := by
  have : IsFibrant (RawOrdinaryJTQuillenTranspose.input W) :=
    OrdinaryJTOrdinaryInputReedy.ordinaryInput_injectiveFibrant W hW
  exact OrdinarySegalConstantIntervalFullyFaithful.mappingMap_weak
    (RawOrdinaryJTQuillenTranspose.input W)
    (OrdinaryJTOrdinaryInputSegal.ordinaryInput_segalCondition W hSegal) x y

#print axioms originalInput_cotensor_segalCondition
#print axioms originalInput_unitRow_diagonal_weak
#print axioms originalInput_constantInterval_mappingMap_weak
#print axioms OrdinarySegalCotensorSegal.cotensor_coherentEvaluation_trivialFibration
#print axioms OrdinaryIntervalPrismTwoTriangleSquare.constantSection_squareIso
#print axioms OrdinaryIntervalPrismTwoTriangleSquare.squareIso_outerPair
#print axioms OrdinaryIntervalPrismTwoTriangleSquare.constantSection_app_zero
#print axioms OrdinarySegalUnitMiddleFibrations.firstCommonFace_fibration
#print axioms KanHomotopyMonomorphismCancellation.weak_pair_of_composite_and_diagonal
#print axioms OrdinarySegalCotensorEndpointCorner.corner_fibration
#print axioms OrdinarySegalTwoTrianglePasting.twoTriangleUnitComparison_weak
#print axioms OrdinarySegalConstantIntervalFullyFaithful.mappingMap_weak
#print axioms JTTheoremCFromOriginalRawOrderedUnit.statement_of_originalRawOrderedUnit

end
end DaggerModels.PartII.OrdinarySegalCotensorFoundationsAudit
