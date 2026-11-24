import DaggerModelsPartII.JTRezkRecognition
import DaggerModelsPartII.JTTheoremCFromStrictification

/-!
# Original Theorem C from the specified raw ordered-unit weakness

This is an implication using the original maps, models, and four-link statement.
The raw ordered-unit input is not proved here. Unlike the target-comma criterion,
this interface does not ask for a new global fixed-Q contraction construction.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTTheoremCFromOriginalRawOrderedUnit

open SegalLocalizers

noncomputable section

private abbrev Source := ReverseDaggerSpace.{0}

local instance : ModelCategory Source := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ

/-- The exact remaining raw ordered-unit input at every specified projective-image pair. -/
def OriginalRawOrderedUnitWeak : Prop :=
  ∀ (W : Source), Localization.localObject localizingFamily W →
    ∀ x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌),
      WeakEquivalence (JTRawOrdinaryAdjoint.rawChosenFiberMapAtP W x y)

/-- The raw ordered-unit input gives weakness of the literal chosen strictification. -/
theorem chosenPsiWeak_of_originalRawOrderedUnit (hRaw : OriginalRawOrderedUnitWeak) :
    JTLocalizedFrameComparison.ChosenPsiWeak := by
  intro W hW
  let f := JTStrictificationInjectiveComparison.comparison W
  have hV := (injectiveLocalObject_iff_strict (JTInjectiveOrderedFiberTransfer.factor W).Z).mp
    (JTInjectiveOrderedFiberTransfer.middle_local W hW)
  have hZ := (injectiveLocalObject_iff_strict (JTStrictificationInjectiveComparison.target W)).mp
    (JTStrictificationInjectiveComparison.target_local W)
  letI := hV.1
  letI := hZ.1
  letI : WeakEquivalence f := JTRezkRecognition.weak_of_ordered_fibers_and_components
    f hV.2 hZ.2
    (JTStrictificationInjectiveComparison.comparison_components_surjective W)
    (JTStrictificationInjectiveComparison.comparison_strictFiber_weak W hW
      (hRaw W hW))
  apply JTStrictificationInjectiveComparison.chosenPsi_local_of_comparison_local W
  exact Localization.weakEquivalences_le_localEquivalences localizingFamily f
    ((weakEquivalence_iff f).mp inferInstance)

/-- The same input implies all four links of the unchanged original Theorem C. -/
theorem statement_of_originalRawOrderedUnit (hRaw : OriginalRawOrderedUnitWeak) :
    TheoremCStatement.statement :=
  TheoremCStatement.statement_of_chosenPsi (chosenPsiWeak_of_originalRawOrderedUnit hRaw)

#print axioms chosenPsiWeak_of_originalRawOrderedUnit
#print axioms statement_of_originalRawOrderedUnit

end
end DaggerModels.PartII.JTTheoremCFromOriginalRawOrderedUnit
