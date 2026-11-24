import DaggerModelsPartII.JTRelativeSegal
import DaggerModelsPartII.JTRelativeRows
import DaggerModelsPartII.JTSegalRowWeakRecognition

/-! The exact relative comparison is weak when the original ordered mapping
spaces are weak, for injectively fibrant Segal diagrams. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTRelativeRowWeak

open SegalLocalizers JTZeroCoskeleton JTProjectiveOrderedFiberComparison

private abbrev S := ReverseDaggerSpace.{0}
private abbrev J := ReverseSimplexᵒᵖ

noncomputable local instance : ModelCategory S := InjectiveKanDiagram.modelCategory J

/-- Every original row of an injectively fibrant reversal diagram is Kan. -/
theorem row_fibrant (W : S) [IsFibrant W] (j : J) : IsFibrant (W.obj j) :=
  (ProjectiveKanDiagram.model_isFibrant_iff J W).mp
    (ProjectiveInjectiveComparison.isFibrant_projective J W inferInstance) j

/-- For the actual relative comparison over the source zero row, the
original ordered strict fibers suffice to detect its rowwise weakness. -/
theorem relative_weak {W Z : S} [IsFibrant W] [IsFibrant Z] (f : W ⟶ Z)
    (hW : segalCondition W) (hZ : segalCondition Z)
    (hf : ∀ x y : (row W ⦋0⦌).obj (op ⦋0⦌), WeakEquivalence
      (JTInjectiveOrderedFiberTransfer.strictFiberMap f x y)) :
    WeakEquivalence (relativeComparison f) := by
  letI := row_fibrant W (op ⟨0⟩)
  letI := targetOverZero_fibrant f
  letI := JTRelativeRows.relative_zero_isIso f
  letI := JTRelativeRows.relative_one_weak f hf
  exact JTSegalRowWeakRecognition.weak_of_zero_one (relativeComparison f) hW
    (JTRelativeSegal.targetOverZero_segal f hZ)

end DaggerModels.PartII.JTRelativeRowWeak
