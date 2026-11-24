import OrdinaryCoherentArrowNaturality
import OrdinarySegalCoherentEvaluationTrivialFibration
import OrdinaryCSSConditions

/-!
# Completeness at the original selected coherent endpoint

The completeness localizer selects vertex zero of the original walking
isomorphism. Coherent edge evaluation identifies its mapping test with the
endpoint map on the actual coherent-arrow component image. The selected
horizontal operator is written literally to keep the vertex convention fixed.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryCoherentCompletenessCriterion

open OrdinaryCSSLocalization (Space completenessMap)
open OrdinarySegalCoherentArrowImage (coherentArrowSubcomplex coherentEvaluation)
open OrdinarySegalWalkingEvaluation (simplexMappingIso)

noncomputable section

/-- The actual coherent-arrow endpoint at the original selected vertex zero. -/
def endpoint (W : Space) :
    (coherentArrowSubcomplex W).toSSet ⟶ W.obj (op ⦋0⦌) :=
  (coherentArrowSubcomplex W).ι ≫
    W.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ (0 : Fin 2)).op

/-- The endpoint square keeps the original whole target map. -/
theorem endpoint_natural {W Z : Space} (f : W ⟶ Z) :
    OrdinaryCoherentArrowNaturality.coherentArrowMap f ≫ endpoint Z =
      endpoint W ≫ f.app (op ⦋0⦌) := by
  dsimp only [endpoint]
  rw [← Category.assoc, OrdinaryCoherentArrowNaturality.coherentArrowMap_inclusion,
    Category.assoc, ← f.naturality, ← Category.assoc]

/-- The chosen completeness test agrees with coherent evaluation followed
by the same selected endpoint, under the original representable mapping iso. -/
theorem evaluation_endpoint (W : Space) :
    coherentEvaluation W ≫ endpoint W =
      diagramMappingPrecomp completenessMap W ≫ (simplexMappingIso W 0).hom := by
  rw [endpoint, ← Category.assoc,
    OrdinarySegalCoherentArrowImage.coherentEvaluation_inclusion]
  exact OrdinarySegalWalkingEvaluation.edgeEvaluation_vertex W 0

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- On an actual injectively fibrant Segal space, completeness is equivalent
to weakness of the coherent endpoint at the unchanged selected vertex. -/
theorem completeness_iff_endpoint_weak (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) :
    OrdinaryCSSConditions.completenessCondition W ↔ WeakEquivalence (endpoint W) := by
  have : WeakEquivalence (coherentEvaluation W) :=
    ((mem_trivialFibrations_iff _).mp
      (OrdinarySegalCoherentEvaluationTrivialFibration.coherentEvaluation_trivialFibration
        W hSegal)).2
  calc
    OrdinaryCSSConditions.completenessCondition W ↔
        WeakEquivalence (diagramMappingPrecomp completenessMap W) :=
      (weakEquivalence_iff _).symm
    _ ↔ WeakEquivalence
        (diagramMappingPrecomp completenessMap W ≫ (simplexMappingIso W 0).hom) :=
      (weakEquivalence_postcomp_iff _ (simplexMappingIso W 0).hom).symm
    _ ↔ WeakEquivalence (coherentEvaluation W ≫ endpoint W) := by
      rw [evaluation_endpoint]
    _ ↔ WeakEquivalence (endpoint W) := weakEquivalence_precomp_iff _ _

#print axioms endpoint_natural
#print axioms evaluation_endpoint
#print axioms completeness_iff_endpoint_weak

end

end DaggerModels.PartII.OrdinaryCoherentCompletenessCriterion
