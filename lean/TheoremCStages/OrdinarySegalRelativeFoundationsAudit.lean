import OrdinarySegalRelativeOuterHorn
import OrdinarySegalCompletionFoundationsAudit
import OrdinarySegalOrderedMappingMaps
import OrdinarySegalCompositionChoices
import OrdinaryWalkingAlternatingAttachment
import RelativeHornReversedExtension

/-!
# Relative lifting audited at the original reverse-dagger input

The generic relative outer-horn theorem applies to the actual ordinary input
of the original raw JT transpose. Only the original Kan-injective and dagger
Segal hypotheses are used. This file is a stage audit, not a Comparator
Challenge, and does not establish the original raw ordered unit weakness.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerOriginalOrdinaryKanCoreEdgeMembership DaggerOriginalRightOuterHornInclusions

namespace DaggerModels.PartII.OrdinarySegalRelativeFoundationsAudit

open OrdinaryCSSLocalization (Space)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- Relative right-outer-horn lifting for the exact ordinary input of an
original reverse-dagger Segal object, with the same supplied base simplex. -/
theorem originalInput_relative_right_outer_horn
    (W : SegalLocalizers.ReverseDaggerSpace.{0})
    (hW : letI : ModelCategory SegalLocalizers.ReverseDaggerSpace.{0} :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hSegal : SegalLocalizers.segalCondition W)
    {K L : SSet.{0}} (v : K ⟶ L) [Mono v] (k : ℕ)
    (φ : (Λ[k + 2, Fin.last (k + 2)] : SSet.{0}) ⟶
      diagramRestriction L (RawOrdinaryJTQuillenTranspose.input W).flip)
    (β : (Δ[k + 2] : SSet.{0}) ⟶
      diagramRestriction K (RawOrdinaryJTQuillenTranspose.input W).flip)
    (w : φ ≫ diagramRestrictionPre v (RawOrdinaryJTQuillenTranspose.input W).flip =
      Λ[k + 2, Fin.last (k + 2)].ι ≫ β)
    (he : edgeIsInvertible
      (diagramRestriction L (RawOrdinaryJTQuillenTranspose.input W).flip)
      (SSet.yonedaEquiv (rightOuterLastEdgeInclusion k ≫ φ))) :
    ∃ σ : (Δ[k + 2] : SSet.{0}) ⟶
        diagramRestriction L (RawOrdinaryJTQuillenTranspose.input W).flip,
      φ = Λ[k + 2, Fin.last (k + 2)].ι ≫ σ ∧
        σ ≫ diagramRestrictionPre v (RawOrdinaryJTQuillenTranspose.input W).flip = β := by
  have : IsFibrant (RawOrdinaryJTQuillenTranspose.input W) :=
    OrdinaryJTOrdinaryInputReedy.ordinaryInput_injectiveFibrant W hW
  exact OrdinarySegalRelativeOuterHorn.restriction_right_outer_horn_lift
    (RawOrdinaryJTQuillenTranspose.input W)
    (OrdinaryJTOrdinaryInputSegal.ordinaryInput_segalCondition W hSegal) v k φ β w he

#print axioms originalInput_relative_right_outer_horn
#print axioms OrdinarySegalHorizontalRestrictions.restriction_innerFibration
#print axioms OrdinarySegalOrderedMappingFibres.mappingFiber_isFibrant
#print axioms OrdinarySegalOrderedMappingMaps.mappingMap_fst
#print axioms OrdinarySegalCompositionChoices.forgetChoice_trivialFibration
#print axioms OrdinaryWalkingAlternatingExhaustion.iSup_stage_eq_top
#print axioms OrdinaryWalkingAlternatingAttachment.horn_le_preimage
#print axioms RelativeHornReversedExtension.relative_extension_of_reversed_extension
#print axioms RawOrdinaryJTUnitCSSWeak.rawTranspose_cssWeak
#print axioms JTTheoremCFromOriginalRawOrderedUnit.statement_of_originalRawOrderedUnit

end

end DaggerModels.PartII.OrdinarySegalRelativeFoundationsAudit
