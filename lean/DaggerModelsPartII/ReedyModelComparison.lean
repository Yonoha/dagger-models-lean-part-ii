import DaggerModelsPartII.ReedyProperties
import TopCatModelCategory.QuillenAdjunction

/-! Left properness and the evaluation Quillen adjunctions of the Reedy model. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial

universe u

namespace DaggerModels.PartII

noncomputable section

local instance : HasLimits DaggerSSet.{u} := daggerSSetHasLimits
local instance : HasColimits DaggerSSet.{u} := daggerSSetHasColimits
local instance : ModelCategory DaggerSSet.{u} := DaggerOriginalJoyalModel.standardModelCategory
local instance : ModelCategory ResolutionDiagram.{u} := resolutionReedyModelCategory

/-- Part II, `cs.lem.reedy`: left properness for the exact Reedy classes. -/
theorem resolutionReedy_leftProper
    {X Y X' Y' : ResolutionDiagram.{u}} {f : X ⟶ Y} {i : X ⟶ X'}
    {j : Y ⟶ Y'} {f' : X' ⟶ Y'} (sq : IsPushout f i j f')
    (hf : reedyWeakEquivalences f) (hi : reedyCofibrations i) :
    reedyWeakEquivalences f' := by
  intro k
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, op ⦋n⦌ = k :=
    ⟨k.unop.len, congrArg op (SimplexCategory.ext _ _ rfl)⟩
  have hi' := reedyCofibration_eval i hi n
  have hf' := hf (op ⦋n⦌)
  change weakEquivalences DaggerSSet.{u} (f.app (op ⦋n⦌)) at hf'
  change weakEquivalences DaggerSSet.{u} (f'.app (op ⦋n⦌))
  change DaggerOriginalJoyalModel.standardModelCategory.categoryWithCofibrations.cofibrations
    (i.app (op ⦋n⦌)) at hi'
  change DaggerOriginalJoyalModel.standardModelCategory.categoryWithWeakEquivalences.weakEquivalences
    (f.app (op ⦋n⦌)) at hf'
  change DaggerOriginalJoyalModel.standardModelCategory.categoryWithWeakEquivalences.weakEquivalences
    (f'.app (op ⦋n⦌))
  rw [DaggerOriginalJoyalModel.standard_model_cof] at hi'
  rw [DaggerOriginalJoyalModel.standard_model_weak] at hf' ⊢
  exact DaggerOriginalJoyalModel.leftProper DaggerUnitaryInvariance.standardReplacement
    (sq.map ((evaluation _ _).obj (op ⦋n⦌))) hf' hi'

/-- Part II, `cs.lem.evaluation-quillen`: evaluation is right Quillen in every degree. -/
theorem evaluationAdjunction_isQuillen (n : ℕ) :
    (evaluationAdjunction.{u} n).IsQuillenAdjunction := by
  letI : (evaluationAt.{u} n).PreservesFibrations :=
    (evaluationAt n).preservesFibrations_iff.mpr
      (fun _ _ f hf ↦ reedyFibration_eval f hf n)
  have hTF : (evaluationAt.{u} n).PreservesTrivialFibrations :=
    ⟨fun _ _ f hf ↦ reedyTrivialFibration_eval f hf n⟩
  letI : (externalTensorWith (Δ[n] : SSet.{u})).PreservesCofibrations :=
    (evaluationAdjunction n).preservesTrivialFibrations_iff_preservesCofibrations.mp hTF
  exact ⟨⟩

/-- The constant-diagram adjunction with evaluation at zero is Quillen before localization. -/
theorem constantEvaluationAdjunction_isQuillen :
    constantEvaluationAdjunction.{u}.IsQuillenAdjunction := by
  letI : (evaluationAt.{u} 0).PreservesFibrations :=
    (evaluationAdjunction_isQuillen 0).toPreservesFibrations
  have hTF := (evaluationAdjunction_isQuillen.{u} 0).preservesTrivialFibrations
  letI : constantDiagram.{u}.PreservesCofibrations :=
    constantEvaluationAdjunction.preservesTrivialFibrations_iff_preservesCofibrations.mp hTF
  exact ⟨⟩

end

end DaggerModels.PartII
