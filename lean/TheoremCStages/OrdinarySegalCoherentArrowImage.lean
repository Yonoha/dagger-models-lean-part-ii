import OrdinarySegalWalkingEvaluation
import OrdinarySegalComponentImage
import NativeFibrationSurjectiveComponents

/-!
# Component-saturated coherent ordinary isomorphism arrows

Evaluate maps from the original walking isomorphism at its original directed
edge. Its component-saturated image is a literal Kan subcomplex of the actual
row of arrows on an injectively Kan fibrant simplicial space. The evaluation
onto that subcomplex is a Kan fibration surjective in every degree.

This constructs the coherent-isomorphism image, not the comparison with
isomorphisms in the Segal homotopy category. In particular neither contractible
fibers nor Rezk Theorem 6.2, the CSS-to-DK theorem, or Theorem C is asserted.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalCoherentArrowImage

open OrdinarySegalWalkingEvaluation OrdinarySegalComponentImage

noncomputable section

private abbrev Space := OrdinaryCSSLocalization.Space

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- The actual arrow components met by coherent walking-isomorphism diagrams. -/
def coherentArrowSubcomplex (W : Space) : (W.obj (op ⦋1⦌)).Subcomplex :=
  componentImage (edgeEvaluation W)

/-- Evaluation with its target narrowed to those actual components. -/
def coherentEvaluation (W : Space) :
    walkingMapping W ⟶ (coherentArrowSubcomplex W).toSSet :=
  factor (edgeEvaluation W)

/-- The factor retains the whole original evaluation map. -/
theorem coherentEvaluation_inclusion (W : Space) :
    coherentEvaluation W ≫ (coherentArrowSubcomplex W).ι = edgeEvaluation W :=
  factor_inclusion _

/-- The actual coherent-arrow image is Kan, including its full simplicial structure. -/
theorem coherentArrow_isFibrant (W : Space) [IsFibrant W] :
    IsFibrant (coherentArrowSubcomplex W).toSSet := by
  have : IsFibrant (W.obj (op ⦋1⦌)) := row_isFibrant W 1
  exact OrdinarySegalComponentSubcomplex.selected_isFibrant _ _

/-- The coherent-arrow inclusion is a fibration of the original Kan model. -/
theorem coherentArrow_inclusion_fibration (W : Space) :
    Fibration (coherentArrowSubcomplex W).ι :=
  OrdinarySegalComponentSubcomplex.inclusion_fibration _ _

/-- Narrowing the target of the actual walking evaluation preserves its Kan lifting. -/
theorem coherentEvaluation_fibration (W : Space) [IsFibrant W] :
    Fibration (coherentEvaluation W) := by
  have : Fibration (edgeEvaluation W) := edgeEvaluation_fibration W
  exact factor_fibration _

/-- Every actual component of coherent arrows is met by the same evaluation. -/
theorem coherentEvaluation_surjective_components (W : Space) :
    Function.Surjective (SSet.mapπ₀ (coherentEvaluation W)) :=
  factor_surjective_components _

/-- A Kan-injectively fibrant target has a coherent lift of every simplex
in its coherent-arrow component image, not just a representative component. -/
theorem coherentEvaluation_degree_surjective (W : Space) [IsFibrant W] (n : ℕ) :
    Function.Surjective ((coherentEvaluation W).app (op ⦋n⦌)) := by
  have : Fibration (coherentEvaluation W) := coherentEvaluation_fibration W
  exact DaggerNativeFibrationSurjectiveComponents.degree_surjective_of_components
    (coherentEvaluation W) (coherentEvaluation_surjective_components W) n

/-- Fibrancy makes the literal range already saturated in arrow components. -/
theorem range_edgeEvaluation (W : Space) [IsFibrant W] :
    SSet.Subcomplex.range (edgeEvaluation W) = coherentArrowSubcomplex W := by
  ext q y
  constructor
  · rintro ⟨x, rfl⟩
    exact ((coherentEvaluation W).app q x).property
  · intro hy
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, op ⦋n⦌ = q :=
      ⟨q.unop.len, congrArg op (SimplexCategory.ext _ _ rfl)⟩
    obtain ⟨x, hx⟩ := coherentEvaluation_degree_surjective W n ⟨y, hy⟩
    exact ⟨x, congrArg Subtype.val hx⟩

#print axioms coherentArrow_isFibrant
#print axioms coherentArrow_inclusion_fibration
#print axioms coherentEvaluation_fibration
#print axioms coherentEvaluation_surjective_components
#print axioms coherentEvaluation_degree_surjective
#print axioms range_edgeEvaluation

end

end DaggerModels.PartII.OrdinarySegalCoherentArrowImage
