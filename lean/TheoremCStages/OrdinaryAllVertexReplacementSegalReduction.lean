import OrdinaryAllVertexDerivedUnit
import OrdinaryAllVertexReplacementComparison

/-!
# Actual all-vertex unit comparisons after a rowwise fibrant replacement

The derived-unit premise of the replacement comparison is discharged by the
checked complete comma descent. The replacement need only be injectively
fibrant and rowwise weak from the original corrected precompletion. Its Segal
condition is not assumed. Segal descent from the relative target is separate.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryAllVertexReplacementSegalReduction

open OrdinaryCSSLocalization (Space)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- The actual unit followed by any specified weak fibrant replacement has
weak all-vertex squares, with no Segal premise on the replacement. -/
theorem replacement_vertexComparison_weak
    (W : Space) [IsFibrant W] (hSegal : OrdinaryCSSConditions.segalCondition W)
    (R : Space) [IsFibrant R]
    (i : OrdinarySegalVerticalPrecompletion.precompletion W ⟶ R)
    (hi : ∀ j : SimplexCategoryᵒᵖ, WeakEquivalence (i.app j)) (n : ℕ) :
    WeakEquivalence (OrdinaryAllVertexSquareComparison.vertexComparison
      (OrdinarySegalVerticalPrecompletion.unit W ≫ i) n) := by
  apply OrdinaryAllVertexReplacementComparison.replacement_vertexComparison_weak W R i hi
  intro m b
  exact OrdinaryAllVertexDerivedUnit.canonicalDerivedTupleMap_weak W hSegal m b

/-- The original relative comparison is weak in all horizontal rows. -/
theorem replacement_relativeComparison_weak
    (W : Space) [IsFibrant W] (hSegal : OrdinaryCSSConditions.segalCondition W)
    (R : Space) [IsFibrant R]
    (i : OrdinarySegalVerticalPrecompletion.precompletion W ⟶ R)
    (hi : ∀ j : SimplexCategoryᵒᵖ, WeakEquivalence (i.app j)) :
    WeakEquivalence (OrdinaryZeroCoskeleton.relativeComparison
      (OrdinarySegalVerticalPrecompletion.unit W ≫ i)) := by
  apply OrdinaryRelativeSegalRecognitionReduction.relativeComparison_weak_of_vertexComparisons
  intro n
  exact replacement_vertexComparison_weak W hSegal R i hi n

/-- The actual relative target is Segal, without assuming that the full
replacement has the Segal condition. -/
theorem replacement_relativeTarget_segal
    (W : Space) [IsFibrant W] (hSegal : OrdinaryCSSConditions.segalCondition W)
    (R : Space) [IsFibrant R]
    (i : OrdinarySegalVerticalPrecompletion.precompletion W ⟶ R)
    (hi : ∀ j : SimplexCategoryᵒᵖ, WeakEquivalence (i.app j)) :
    OrdinaryCSSConditions.segalCondition (OrdinaryZeroCoskeleton.targetOverZero
      (OrdinarySegalVerticalPrecompletion.unit W ≫ i)) := by
  apply OrdinaryRelativeSegalRecognitionReduction.targetOverZero_segal_of_vertexComparisons
    (OrdinarySegalVerticalPrecompletion.unit W ≫ i) hSegal
  intro n
  exact replacement_vertexComparison_weak W hSegal R i hi n

#print axioms replacement_vertexComparison_weak
#print axioms replacement_relativeComparison_weak
#print axioms replacement_relativeTarget_segal

end

end DaggerModels.PartII.OrdinaryAllVertexReplacementSegalReduction
