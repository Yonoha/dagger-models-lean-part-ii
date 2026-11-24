import OrdinaryCotensorWalkingHomotopy
import OrdinaryPrecompletionCategoricalEquivalence

/-!
# Corrected precompletion of the original groupoid-simplex constant sections

The checked whole contraction supplies literal walking inverse data for the
actual constant section and its actual evaluation. The corrected precompletion
therefore takes both original maps to rowwise weak equivalences. No Segal or
completeness assumption on the input space is imposed.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryPrecompletionConstantSectionWeak

open OrdinaryCSSLocalization (Space)
open OrdinarySegalHorizontalCotensor (cotensor)
open OrdinarySegalHorizontalCotensorPoint (constantSection)
open OrdinarySegalCotensorPointEvaluation (evaluation)
open OrdinaryCotensorWalkingHomotopy (chosenVertex categoricalHomotopy)
open OrdinaryPrecompletionWalkingHomotopy (vertexSection)
open OrdinaryPrecompletionCategoricalEquivalence (WalkingInverseData)
open OrdinarySegalVerticalPrecompletionNaturality (precompletionMap)

noncomputable section

private abbrev E (k : SimplexCategory) := GroupoidSimplex.parameter.obj k

/-- The actual groupoid-simplex contraction gives literal inverse data. -/
def constantSectionWalkingInverse (k : SimplexCategory) (j : Fin (k.len + 1))
    (W : Space) : WalkingInverseData (constantSection (E k) W) where
  leftInverse := evaluation (E k) W (JTParameterContraction.parameterVertex k j)
  rightInverse := evaluation (E k) W (JTParameterContraction.parameterVertex k j)
  sourceVertex₀ := chosenVertex 0
  sourceVertex₁ := chosenVertex 1
  sourceHomotopy := prod.fst
  sourceComposite := by
    simpa only [vertexSection, prod.lift_fst] using
      (OrdinaryGroupoidSimplexCotensorHomotopyInverse.section_evaluation k j W).symm
  sourceIdentity := by simp only [vertexSection, prod.lift_fst]
  targetVertex₀ := chosenVertex 1
  targetVertex₁ := chosenVertex 0
  targetHomotopy := categoricalHomotopy k j W
  targetComposite := OrdinaryCotensorWalkingHomotopy.endpoint_one k j W
  targetIdentity := OrdinaryCotensorWalkingHomotopy.endpoint_zero k j W

/-- Every row of the corrected precompletion of the actual constant section is weak. -/
theorem constantSection_row_weak (k : SimplexCategory) (W : Space)
    (n : SimplexCategory) :
    WeakEquivalence ((precompletionMap (constantSection (E k) W)).app (op n)) :=
  OrdinaryPrecompletionCategoricalEquivalence.precompletionMap_row_weak_of_walkingInverse
    (constantSection (E k) W)
    (constantSectionWalkingInverse k ⟨0, Nat.zero_lt_succ _⟩ W) n

/-- Every original specified evaluation also becomes weak in each row. -/
theorem evaluation_row_weak (k : SimplexCategory) (j : Fin (k.len + 1)) (W : Space)
    (n : SimplexCategory) :
    WeakEquivalence ((precompletionMap
      (evaluation (E k) W (JTParameterContraction.parameterVertex k j))).app (op n)) := by
  have : WeakEquivalence ((precompletionMap (constantSection (E k) W)).app (op n)) :=
    constantSection_row_weak k W n
  have h : (precompletionMap (constantSection (E k) W)).app (op n) ≫
      (precompletionMap
        (evaluation (E k) W (JTParameterContraction.parameterVertex k j))).app (op n) =
      𝟙 _ := by
    change ((precompletionMap (constantSection (E k) W) ≫
      precompletionMap (evaluation (E k) W
        (JTParameterContraction.parameterVertex k j))).app (op n)) = _
    rw [← OrdinarySegalVerticalPrecompletionNaturality.precompletionMap_comp,
      OrdinaryGroupoidSimplexCotensorHomotopyInverse.section_evaluation,
      OrdinarySegalVerticalPrecompletionNaturality.precompletionMap_id]
    rfl
  exact weakEquivalence_of_precomp_of_fac h

#print axioms constantSectionWalkingInverse
#print axioms constantSection_row_weak
#print axioms evaluation_row_weak

end

end DaggerModels.PartII.OrdinaryPrecompletionConstantSectionWeak
