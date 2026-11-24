import OrdinaryGroupoidSimplexTransitionAudit
import OrdinaryGroupoidSimplexTransitionEndpointSquare
import OrdinarySegalVerticalPrecompletionFiberComparison
import OrdinarySegalResolutionRelativeReedy

/-!
# Strict precompletion-unit comparison at the actual original JT input

The original input is only assumed Kan-injectively fibrant and Segal. The
target mapping fiber below is the strict pullback of the correctly indexed
precompletion. Its identification with a derived mapping space after fibrant
replacement, the exact raw ordered-unit weakness, and Theorem C are separate
obligations and are not asserted by this audit.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalVerticalPrecompletionUnitAudit

open OrdinaryCSSLocalization (Space)
open OrdinarySegalOrderedMappingMaps (mappingMap)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev input (W : SegalLocalizers.ReverseDaggerSpace.{0}) :=
  RawOrdinaryJTQuillenTranspose.input W

/-- The actual corrected precompletion unit is weak on every strict ordered
mapping fiber at the original ordinary JT input vertices. -/
theorem originalInput_unit_mappingMap_weak
    (W : SegalLocalizers.ReverseDaggerSpace.{0})
    (hW : letI : ModelCategory SegalLocalizers.ReverseDaggerSpace.{0} :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hSegal : SegalLocalizers.segalCondition W)
    (x y : ((input W).obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    WeakEquivalence
      (mappingMap (OrdinarySegalVerticalPrecompletion.unit (input W)) x y) := by
  have : IsFibrant (input W) :=
    OrdinaryJTOrdinaryInputReedy.ordinaryInput_injectiveFibrant W hW
  exact OrdinarySegalVerticalPrecompletionFiberComparison.mappingMap_unit_weak
    (input W) (OrdinaryJTOrdinaryInputSegal.ordinaryInput_segalCondition W hSegal) x y

#print axioms originalInput_unit_mappingMap_weak
#print axioms OrdinarySegalVerticalPrecompletionFiberComparison.mappingMap_unit_weak
#print axioms OrdinarySegalResolutionRelativeReedy.diagonalComparison_weak
#print axioms OrdinaryGroupoidSimplexTransitionEndpointSquare.endpointComparison_weak
#print axioms JTTheoremCFromOriginalRawOrderedUnit.statement_of_originalRawOrderedUnit

end
end DaggerModels.PartII.OrdinarySegalVerticalPrecompletionUnitAudit
