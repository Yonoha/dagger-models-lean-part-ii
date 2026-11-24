import OrdinaryAllVertexReplacementSegalReduction
import OrdinaryAllVertexComponentCover
import OrdinarySegalFullTupleDescent

/-!
# Segal recognition after fibrant replacement of the corrected precompletion

For the actual corrected unit, complete finite vertex-tuple fibers and component
coverage supply the noncircular descent hypotheses. Every injectively fibrant
rowwise weak replacement of the original precompletion is therefore Segal.
Completeness and the original raw ordered unit theorem remain separate.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryPrecompletionReplacementSegal

open OrdinaryCSSLocalization (Space)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- Any actual weak injectively fibrant replacement of the corrected
precompletion of an injectively fibrant Segal space is Segal. -/
theorem replacement_segal (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) (R : Space) [IsFibrant R]
    (i : OrdinarySegalVerticalPrecompletion.precompletion W ⟶ R)
    (hi : ∀ j : SimplexCategoryᵒᵖ, WeakEquivalence (i.app j)) :
    OrdinaryCSSConditions.segalCondition R := by
  apply OrdinarySegalFullTupleDescent.segal_of_relative_and_tuple_surjective
    (OrdinarySegalVerticalPrecompletion.unit W ≫ i)
  · exact OrdinaryAllVertexReplacementSegalReduction.replacement_relativeTarget_segal
      W hSegal R i hi
  · intro n
    exact OrdinaryAllVertexComponentCover.replacement_tuple_components_surjective W R i hi n

#print axioms replacement_segal

end

end DaggerModels.PartII.OrdinaryPrecompletionReplacementSegal
