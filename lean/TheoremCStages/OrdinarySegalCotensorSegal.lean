import OrdinarySegalCotensorMappingIso
import OrdinarySegalCotensorFibrant
import OrdinarySegalInnerAnodyneMapping
import OrdinarySegalLocalization
import OrdinarySegalCoherentEvaluationTrivialFibration

/-!
# The actual horizontal cotensor preserves ordinary Segal fibrancy

Strict Fubini identifies the cotensor's spine restriction with the original
mapping test for the tensor of that same spine. The existing spine is
inner-left, and the checked closed adjunction preserves inner-left maps
under tensor by any parameter. Together with the separately proved base
injective fibrancy this gives fibrancy in the same spine-only Segal model.
No completeness condition or weak-equivalence conclusion is assumed.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra MonoidalCategory
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalCotensorSegal

open OrdinaryCSSLocalization (Space discrete spineMap)
open OrdinarySegalHorizontalCotensor (cotensor)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- The actual cotensor preserves the ordinary Segal condition under the
original base fibrancy hypothesis, for every horizontal parameter. -/
theorem cotensor_segalCondition (K : SSet.{0}) (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) :
    OrdinaryCSSConditions.segalCondition (cotensor K W) := by
  intro n _
  let i := (DaggerNativeStandardSpineInner.spine.{0} n).ι
  have ht := OrdinarySegalInnerAnodyneMapping.tensor_spine_mapping_trivialFibration
    W hSegal K n
  let e : Arrow.mk (diagramMappingPrecomp (spineMap n) (cotensor K W)) ≅
      Arrow.mk (diagramMappingPrecomp (discrete.map (K ◁ i)) W) :=
    Arrow.isoMk (OrdinarySegalCotensorMappingIso.mappingIso K (Δ[n] : SSet.{0}) W)
      (OrdinarySegalCotensorMappingIso.mappingIso K
        (DaggerNativeStandardSpineInner.spine n : SSet.{0}) W)
      (OrdinarySegalCotensorMappingIso.mappingIso_natural_source K i W).symm
  have hs : trivialFibrations SSet.{0}
      (diagramMappingPrecomp (spineMap n) (cotensor K W)) :=
    ((trivialFibrations SSet.{0}).arrow_mk_iso_iff e).mpr ht
  exact (weakEquivalence_iff _).mp ((mem_trivialFibrations_iff _).mp hs).2

/-- Cotensor by any original parameter is fibrant in the unchanged
ordinary spine-only Segal localization. -/
theorem cotensor_segalFibrant (K : SSet.{0}) (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) :
    @IsFibrant Space _ OrdinarySegalLocalization.model.categoryWithFibrations _
      (cotensor K W) := by
  apply (OrdinarySegalLocalization.isFibrant_iff _).mpr
  exact ⟨OrdinarySegalCotensorFibrant.cotensor_injectiveFibrant K W inferInstance,
    cotensor_segalCondition K W hSegal⟩

/-- The same coherent evaluation theorem is available on every actual
horizontal cotensor, without adding ordinary completeness. -/
theorem cotensor_coherentEvaluation_trivialFibration (K : SSet.{0}) (W : Space)
    [IsFibrant W] (hSegal : OrdinaryCSSConditions.segalCondition W) :
    trivialFibrations SSet.{0}
      (OrdinarySegalCoherentArrowImage.coherentEvaluation (cotensor K W)) := by
  have : IsFibrant (cotensor K W) :=
    OrdinarySegalCotensorFibrant.cotensor_injectiveFibrant K W inferInstance
  exact OrdinarySegalCoherentEvaluationTrivialFibration.coherentEvaluation_trivialFibration
    (cotensor K W) (cotensor_segalCondition K W hSegal)

#print axioms cotensor_segalCondition
#print axioms cotensor_segalFibrant
#print axioms cotensor_coherentEvaluation_trivialFibration

end

end DaggerModels.PartII.OrdinarySegalCotensorSegal
