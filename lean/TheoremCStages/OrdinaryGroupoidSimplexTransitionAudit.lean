import OrdinarySegalCoherentTransportAudit
import OrdinarySegalCoherentTargetTransport
import OrdinaryGroupoidSimplexTransitionFullyFaithful
import OrdinarySegalVerticalPrecompletionComponents

/-!
# Ordered fibers of original groupoid-simplex transitions

The actual ordinary JT input inherits coherent target-change invariance
and all original groupoid-simplex transition mapping-fiber equivalences
from the checked ordinary Segal statements. The correctly indexed
precompletion unit covers its object components. These statements do not
assert original raw-unit weakness or Theorem C.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryGroupoidSimplexTransitionAudit

open OrdinaryCSSLocalization (Space)
open OrdinarySegalHorizontalCotensor (cotensor)
open OrdinarySegalOrderedMappingMaps (mappingMap)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev E (k : SimplexCategory) : SSet.{0} :=
  GroupoidSimplex.parameter.obj k
private abbrev input (W : SegalLocalizers.ReverseDaggerSpace.{0}) :=
  RawOrdinaryJTQuillenTranspose.input W

/-- Coherent target change compares the original ordered mapping fibers
at the two actual vertices of the same whole `E[1]` map. -/
theorem originalInput_mappingMap_weak_iff_target
    (W : SegalLocalizers.ReverseDaggerSpace.{0})
    (hW : letI : ModelCategory SegalLocalizers.ReverseDaggerSpace.{0} :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hSegal : SegalLocalizers.segalCondition W)
    (V : Space) [IsFibrant V] (hV : OrdinaryCSSConditions.segalCondition V)
    (f : input W ⟶ V) (H : E ⦋1⦌ ⟶ (input W).flip.obj (op ⦋0⦌))
    (x : ((input W).obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    WeakEquivalence (mappingMap f x
      (SSet.yonedaEquiv (X := (input W).flip.obj (op ⦋0⦌)) (n := ⦋0⦌)
        (JTParameterContraction.parameterVertex ⦋1⦌ 0 ≫ H))) ↔
    WeakEquivalence (mappingMap f x
      (SSet.yonedaEquiv (X := (input W).flip.obj (op ⦋0⦌)) (n := ⦋0⦌)
        (JTParameterContraction.parameterVertex ⦋1⦌ 1 ≫ H))) := by
  have : IsFibrant (input W) :=
    OrdinaryJTOrdinaryInputReedy.ordinaryInput_injectiveFibrant W hW
  exact OrdinarySegalCoherentTargetTransport.mappingMap_weak_iff_actual f
    (OrdinaryJTOrdinaryInputSegal.ordinaryInput_segalCondition W hSegal) hV H x

/-- Every original simplex operator induces a weak map on each ordered
mapping fiber of the cotensors of the actual ordinary JT input. -/
theorem originalInput_transition_mappingMap_weak
    {n m : SimplexCategory} (θ : n ⟶ m)
    (W : SegalLocalizers.ReverseDaggerSpace.{0})
    (hW : letI : ModelCategory SegalLocalizers.ReverseDaggerSpace.{0} :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hSegal : SegalLocalizers.segalCondition W)
    (z z' : ((cotensor (E m) (input W)).obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    WeakEquivalence
      (mappingMap
        (OrdinaryGroupoidSimplexCotensorTransitionHomotopy.transition θ (input W))
        z z') := by
  have : IsFibrant (input W) :=
    OrdinaryJTOrdinaryInputReedy.ordinaryInput_injectiveFibrant W hW
  exact OrdinaryGroupoidSimplexTransitionFullyFaithful.mappingMap_weak θ (input W)
    (OrdinaryJTOrdinaryInputSegal.ordinaryInput_segalCondition W hSegal) z z'

/-- The correctly indexed precompletion unit of the actual original input
is surjective on components of its object row. -/
theorem originalInput_precompletion_unit_object_components_surjective
    (W : SegalLocalizers.ReverseDaggerSpace.{0}) :
    Function.Surjective
      (SSet.mapπ₀
        ((OrdinarySegalVerticalPrecompletion.unit (input W)).app (op ⦋0⦌))) :=
  OrdinarySegalVerticalPrecompletionComponents.unit_object_components_surjective
    (input W)

#print axioms originalInput_mappingMap_weak_iff_target
#print axioms originalInput_transition_mappingMap_weak
#print axioms originalInput_precompletion_unit_object_components_surjective
#print axioms OrdinaryGroupoidSimplexTransitionFullyFaithful.mappingMap_weak
#print axioms OrdinarySegalCoherentTargetTransport.mappingMap_weak_iff_actual
#print axioms JTTheoremCFromOriginalRawOrderedUnit.statement_of_originalRawOrderedUnit

end
end DaggerModels.PartII.OrdinaryGroupoidSimplexTransitionAudit
