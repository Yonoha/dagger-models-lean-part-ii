import OrdinaryPrecompletionCSSReplacement
import OrdinaryCoherentWeakInvariance

/-!
# A chosen actual fibrant replacement of corrected precompletion

Use Mathlib's existing trivial-cofibration/fibration factorization in the
original injective Kan model. The complete Segal theorem applies to exactly
this replacement and its actual map. No complete-input premise is introduced.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryChosenCSSCompletion

open OrdinaryCSSLocalization (Space)
open OrdinarySegalVerticalPrecompletion (precompletion)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- The standard model-category factorization of the actual terminal map. -/
def factor (W : Space) :=
  factorizationData (trivialCofibrations Space) (fibrations Space)
    (terminal.from (precompletion W))

/-- The chosen injectively fibrant replacement of the corrected precompletion. -/
def completion (W : Space) : Space := (factor W).Z

/-- The actual first map of that fixed factorization. -/
def inclusion (W : Space) : precompletion W ⟶ completion W := (factor W).i

/-- The original corrected unit followed by the specified chosen replacement. -/
def unit (W : Space) : W ⟶ completion W :=
  OrdinarySegalVerticalPrecompletion.unit W ≫ inclusion W

/-- The chosen replacement map is weak in the original injective Kan model. -/
theorem inclusion_baseWeak (W : Space) : WeakEquivalence (inclusion W) :=
  (weakEquivalence_iff _).mpr (factor W).hi.2

/-- Its cofibration class is the original monomorphism class. -/
theorem inclusion_mono (W : Space) : Mono (inclusion W) := by
  have h := (factor W).hi.1
  rw [InjectiveKanDiagram.model_cofibrations] at h
  exact h

/-- The chosen object is genuinely injectively fibrant. -/
theorem completion_injectiveFibrant (W : Space) : IsFibrant (completion W) := by
  haveI : Fibration (factor W).p := (fibration_iff _).mpr (factor W).hp
  exact (isFibrant_iff_of_isTerminal (factor W).p terminalIsTerminal).mpr inferInstance

/-- The same chosen replacement map is weak in every horizontal row. -/
theorem inclusion_rowWeak (W : Space) (q : SimplexCategoryᵒᵖ) :
    WeakEquivalence ((inclusion W).app q) := by
  haveI : WeakEquivalence (inclusion W) := inclusion_baseWeak W
  exact OrdinaryCoherentWeakInvariance.row_weak (inclusion W) q

/-- A base weak map is weak in the exact chosen ordinary CSS localization. -/
theorem inclusion_cssWeak (W : Space) :
    OrdinaryCSSLocalization.model.categoryWithWeakEquivalences.weakEquivalences
      (inclusion W) := by
  rw [OrdinaryCSSLocalization.exactClasses.2]
  haveI : WeakEquivalence (inclusion W) := inclusion_baseWeak W
  exact Localization.weakEquivalences_le_localEquivalences
    OrdinaryCSSLocalization.localizingFamily (inclusion W) (mem_weakEquivalences _)

/-- For the original fibrant Segal hypotheses, this same chosen object is
fibrant in the actual ordinary CSS model. -/
theorem completion_cssFibrant (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) :
    @IsFibrant Space _ OrdinaryCSSLocalization.model.categoryWithFibrations _
      (completion W) := by
  haveI : IsFibrant (completion W) := completion_injectiveFibrant W
  exact OrdinaryPrecompletionCSSReplacement.replacement_cssFibrant
    W hSegal (completion W) (inclusion W) (inclusion_rowWeak W)

#print axioms inclusion_baseWeak
#print axioms inclusion_mono
#print axioms completion_injectiveFibrant
#print axioms inclusion_cssWeak
#print axioms completion_cssFibrant

end

end DaggerModels.PartII.OrdinaryChosenCSSCompletion
