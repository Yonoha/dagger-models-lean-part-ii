import OrdinaryCoherentDiagonalSubcomplex
import OrdinaryCoherentReplacementVertexPreimage
import OrdinaryPrecompletionCompletenessReduction

/-!
# Completeness of the actual fibrant replacement of corrected precompletion

The literal coherent diagonal range is detected by its original first vertex.
Exact coherent reflection of the same unit and replacement identifies that
vertex preimage. Naturality extends this to every simplicial degree. Native
right properness then makes the original coherent comparison weak, and its
checked endpoint criterion gives completeness of the specified replacement.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryPrecompletionReplacementComplete

open OrdinaryCSSLocalization (Space)
open OrdinarySegalVerticalPrecompletion (precompletion)
open OrdinaryCoherentReplacementComparison (diagonalInclusion coherentComparison)
open OrdinarySegalCoherentArrowImage (coherentArrowSubcomplex)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- The literal coherent diagonal range is the exact preimage of the specified
replacement coherent image in every degree, retaining the original map. -/
theorem replacement_coherent_preimage (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) (R : Space) [IsFibrant R]
    (i : precompletion W ⟶ R)
    (hi : ∀ j : SimplexCategoryᵒᵖ, WeakEquivalence (i.app j))
    (q : SimplexCategoryᵒᵖ) (x : ((precompletion W).obj (op ⦋1⦌)).obj q) :
    x ∈ (SSet.Subcomplex.range (diagonalInclusion W)).obj q ↔
      (i.app (op ⦋1⦌)).app q x ∈ (coherentArrowSubcomplex R).obj q := by
  let a : q ⟶ op ⦋0⦌ := (SimplexCategory.const ⦋0⦌ q.unop 0).op
  calc
    x ∈ (SSet.Subcomplex.range (diagonalInclusion W)).obj q ↔
        ((precompletion W).obj (op ⦋1⦌)).map a x ∈
          (SSet.Subcomplex.range (diagonalInclusion W)).obj (op ⦋0⦌) :=
      OrdinaryCoherentDiagonalSubcomplex.range_first_vertex_iff W hSegal q x
    _ ↔ (i.app (op ⦋1⦌)).app (op ⦋0⦌)
        (((precompletion W).obj (op ⦋1⦌)).map a x) ∈
          (coherentArrowSubcomplex R).obj (op ⦋0⦌) :=
      OrdinaryCoherentReplacementVertexPreimage.replacement_vertex_preimage
        W hSegal R i hi _
    _ ↔ (R.obj (op ⦋1⦌)).map a ((i.app (op ⦋1⦌)).app q x) ∈
        (coherentArrowSubcomplex R).obj (op ⦋0⦌) := by
      have h := congrFun ((i.app (op ⦋1⦌)).naturality a) x
      exact Iff.of_eq (congrArg
        (fun y ↦ y ∈ (coherentArrowSubcomplex R).obj (op ⦋0⦌)) h)
    _ ↔ (i.app (op ⦋1⦌)).app q x ∈ (coherentArrowSubcomplex R).obj q :=
      (OrdinaryCoherentDiagonalSubcomplex.mem_coherent_first R q _).symm

/-- The same actual coherent comparison into the specified replacement is weak. -/
theorem replacement_coherentComparison_weak (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) (R : Space) [IsFibrant R]
    (i : precompletion W ⟶ R)
    (hi : ∀ j : SimplexCategoryᵒᵖ, WeakEquivalence (i.app j)) :
    WeakEquivalence (coherentComparison W R hSegal i) :=
  OrdinaryCoherentReplacementPreimage.coherentComparison_weak_of_preimage
    W R hSegal i (hi _) (replacement_coherent_preimage W hSegal R i hi)

/-- Every injectively fibrant rowwise weak replacement of the original
corrected precompletion of a fibrant Segal input is complete. -/
theorem replacement_complete (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) (R : Space) [IsFibrant R]
    (i : precompletion W ⟶ R)
    (hi : ∀ j : SimplexCategoryᵒᵖ, WeakEquivalence (i.app j)) :
    OrdinaryCSSConditions.completenessCondition R :=
  (OrdinaryPrecompletionCompletenessReduction.completeness_iff_coherentComparison_weak
    W hSegal R i hi).mpr (replacement_coherentComparison_weak W hSegal R i hi)

/-- The actual replacement is a complete Segal space, with both conditions
proved from the same original input and replacement hypotheses. -/
theorem replacement_completeSegalCondition (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) (R : Space) [IsFibrant R]
    (i : precompletion W ⟶ R)
    (hi : ∀ j : SimplexCategoryᵒᵖ, WeakEquivalence (i.app j)) :
    OrdinaryCSSConditions.completeSegalCondition R :=
  ⟨OrdinaryPrecompletionReplacementSegal.replacement_segal W hSegal R i hi,
    replacement_complete W hSegal R i hi⟩

#print axioms replacement_coherent_preimage
#print axioms replacement_coherentComparison_weak
#print axioms replacement_complete
#print axioms replacement_completeSegalCondition

end

end DaggerModels.PartII.OrdinaryPrecompletionReplacementComplete
