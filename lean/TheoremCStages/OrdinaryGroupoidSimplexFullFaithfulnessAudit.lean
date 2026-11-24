import OrdinaryGroupoidSimplexComparisonAudit
import OrdinarySegalConstantGroupoidSimplexFullyFaithful

/-!
# Full faithfulness for every original groupoid-simplex constant section

The unchanged original ordinary JT input satisfies the required injective
Kan fibrancy and Segal condition. Every original `E[n]` constant section
therefore induces weak equivalences on its exact ordered mapping fibers.
The selected contraction vertex is constructed internally; it is not an
additional hypothesis on the original input or either source object.

This does not identify the constant section with the original raw transpose,
prove arbitrary-object transition DK recognition, or prove Theorem C.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryGroupoidSimplexFullFaithfulnessAudit

noncomputable section

private local instance : ModelCategory OrdinaryCSSLocalization.Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- Every original constant groupoid-simplex section is weak on all the
literal ordered mapping fibers of the unchanged original JT input. -/
theorem originalInput_constantGroupoidSimplex_mappingMap_weak
    (W : SegalLocalizers.ReverseDaggerSpace.{0})
    (hW : letI : ModelCategory SegalLocalizers.ReverseDaggerSpace.{0} :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hSegal : SegalLocalizers.segalCondition W) (k : SimplexCategory)
    (x y : ((RawOrdinaryJTQuillenTranspose.input W).obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    WeakEquivalence (OrdinarySegalOrderedMappingMaps.mappingMap
      (OrdinarySegalHorizontalCotensorPoint.constantSection
        (GroupoidSimplex.parameter.obj k) (RawOrdinaryJTQuillenTranspose.input W)) x y) := by
  have : IsFibrant (RawOrdinaryJTQuillenTranspose.input W) :=
    OrdinaryJTOrdinaryInputReedy.ordinaryInput_injectiveFibrant W hW
  exact OrdinarySegalConstantGroupoidSimplexFullyFaithful.mappingMap_weak
    (RawOrdinaryJTQuillenTranspose.input W)
    (OrdinaryJTOrdinaryInputSegal.ordinaryInput_segalCondition W hSegal) k 0 x y

#print axioms originalInput_constantGroupoidSimplex_mappingMap_weak
#print axioms OrdinarySegalConstantGroupoidSimplexFullyFaithful.mappingMap_weak
#print axioms OrdinaryGroupoidSimplexComparisonAudit.originalInput_coherent_object_witness
#print axioms OrdinaryGroupoidSimplexComparisonAudit.originalInput_transition_inverse_composites
#print axioms OrdinarySegalOrderedMappingRetracts.mappingRetract
#print axioms JTTheoremCFromOriginalRawOrderedUnit.statement_of_originalRawOrderedUnit

end
end DaggerModels.PartII.OrdinaryGroupoidSimplexFullFaithfulnessAudit
