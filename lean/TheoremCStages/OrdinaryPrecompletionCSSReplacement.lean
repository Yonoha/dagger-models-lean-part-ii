import OrdinaryPrecompletionReplacementComplete

/-!
# The actual replacement is fibrant in the original ordinary CSS model

Apply the already checked strict-condition recognition for the exact chosen
localization family. The replacement retains its specified rowwise weak map
from corrected precompletion; the original Segal input need not be complete.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryPrecompletionCSSReplacement

open OrdinaryCSSLocalization (Space localizingFamily)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- The same specified replacement is local for the original ordinary CSS family. -/
theorem replacement_localObject (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) (R : Space) [IsFibrant R]
    (i : OrdinarySegalVerticalPrecompletion.precompletion W ⟶ R)
    (hi : ∀ j : SimplexCategoryᵒᵖ, WeakEquivalence (i.app j)) :
    Localization.localObject localizingFamily R :=
  (OrdinaryCSSConditions.localObject_iff_strict R).mpr
    ⟨inferInstance,
      OrdinaryPrecompletionReplacementComplete.replacement_completeSegalCondition
        W hSegal R i hi⟩

/-- Fibrancy holds in the actual ordinary complete Segal localization. -/
theorem replacement_cssFibrant (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) (R : Space) [IsFibrant R]
    (i : OrdinarySegalVerticalPrecompletion.precompletion W ⟶ R)
    (hi : ∀ j : SimplexCategoryᵒᵖ, WeakEquivalence (i.app j)) :
    @IsFibrant Space _ OrdinaryCSSLocalization.model.categoryWithFibrations _ R :=
  (OrdinaryCSSConditions.isFibrant_iff R).mpr
    ⟨inferInstance,
      OrdinaryPrecompletionReplacementComplete.replacement_completeSegalCondition
        W hSegal R i hi⟩

#print axioms replacement_localObject
#print axioms replacement_cssFibrant

end

end DaggerModels.PartII.OrdinaryPrecompletionCSSReplacement
