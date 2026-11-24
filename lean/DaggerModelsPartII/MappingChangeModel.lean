import DaggerModelsPartII.HomotopyMappingEquivalence

/-! Two model structures with the same cofibrations share the same source resolutions. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite Simplicial
open scoped SSet.modelCategoryQuillen

universe v u

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]

omit [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C] in
private theorem trivialFibrations_eq_of_cofibrations_eq (M N : ModelCategory C)
    (h : M.categoryWithCofibrations.cofibrations = N.categoryWithCofibrations.cofibrations) :
    @trivialFibrations C _ M.categoryWithFibrations M.categoryWithWeakEquivalences =
      @trivialFibrations C _ N.categoryWithFibrations N.categoryWithWeakEquivalences := by
  have hM : M.categoryWithCofibrations.cofibrations.rlp =
      @trivialFibrations C _ M.categoryWithFibrations M.categoryWithWeakEquivalences := by
    letI := M
    exact rlp_eq_of_wfs (cofibrations C) (trivialFibrations C)
  have hN : N.categoryWithCofibrations.cofibrations.rlp =
      @trivialFibrations C _ N.categoryWithFibrations N.categoryWithWeakEquivalences := by
    letI := N
    exact rlp_eq_of_wfs (cofibrations C) (trivialFibrations C)
  rw [← hM, ← hN, h]

private def CosimplicialResolution.changeModel (M N : ModelCategory C)
    (h : M.categoryWithCofibrations.cofibrations = N.categoryWithCofibrations.cofibrations) {X : C}
    (R : @CosimplicialResolution C _ M _ _ X) :
    @CosimplicialResolution C _ N _ _ X where
  oppositeDiagram := (@CosimplicialResolution.oppositeDiagram C _ M _ _ X R)
  augmentationOp := (@CosimplicialResolution.augmentationOp C _ M _ _ X R)
  augmentationOp_mem := by
    have hM : reedyLatchingProperty
        ((@trivialFibrations C _ M.categoryWithFibrations M.categoryWithWeakEquivalences).op)
        (@CosimplicialResolution.augmentationOp C _ M _ _ X R) := by
      letI := M
      have hR := (@CosimplicialResolution.augmentationOp_mem C _ M _ _ X R)
      change (reedyLatchingProperty (cofibrations Cᵒᵖ) ⊓ simplicialReedyWeakEquivalences Cᵒᵖ)
        (@CosimplicialResolution.augmentationOp C _ M _ _ X R) at hR
      rw [simplicialReedyCofibrations_inf_weakEquivalences, trivialCofibrations_op] at hR
      exact hR
    letI := N
    change (reedyLatchingProperty (cofibrations Cᵒᵖ) ⊓ simplicialReedyWeakEquivalences Cᵒᵖ)
      (@CosimplicialResolution.augmentationOp C _ M _ _ X R)
    rw [simplicialReedyCofibrations_inf_weakEquivalences, trivialCofibrations_op]
    exact trivialFibrations_eq_of_cofibrations_eq M N h ▸ hM
  fibrantOp := by
    have hM : ∀ n, M.categoryWithCofibrations.cofibrations.op ((matchingComparison n).app (@CosimplicialResolution.oppositeDiagram C _ M _ _ X R)) := by
      letI := M
      exact (reedyFibrant_iff_matchingComparison (@CosimplicialResolution.oppositeDiagram C _ M _ _ X R)).mp (@CosimplicialResolution.fibrantOp C _ M _ _ X R)
    letI := N
    apply (reedyFibrant_iff_matchingComparison (@CosimplicialResolution.oppositeDiagram C _ M _ _ X R)).mpr
    change ∀ n, N.categoryWithCofibrations.cofibrations.op ((matchingComparison n).app (@CosimplicialResolution.oppositeDiagram C _ M _ _ X R))
    rw [← h]
    exact hM

/-- For a common fibrant target, changing the model structure without changing its
cofibrations preserves the derived mapping-space test. -/
theorem homotopyMappingWeakEquivalences_iff_of_cofibrations_eq (M N : ModelCategory C)
    (h : M.categoryWithCofibrations.cofibrations = N.categoryWithCofibrations.cofibrations) (Z : C)
    (hM : @IsFibrant C _ M.categoryWithFibrations _ Z)
    (hN : @IsFibrant C _ N.categoryWithFibrations _ Z) {X Y : C} (f : X ⟶ Y) :
    @homotopyMappingWeakEquivalences C _ M _ _ Z _ _ f ↔
      @homotopyMappingWeakEquivalences C _ N _ _ Z _ _ f := by
  let R := @cosimplicialResolution C _ M _ _ X
  let S := @cosimplicialResolution C _ M _ _ Y
  let g := by
    letI := M
    exact R.comparison S f
  let R' := CosimplicialResolution.changeModel M N h R
  let S' := CosimplicialResolution.changeModel M N h S
  let g' := by
    letI := N
    exact (⟨@CosimplicialResolution.Comparison.mapOp C _ M _ _ X R Y S f g,
      @CosimplicialResolution.Comparison.comm C _ M _ _ X R Y S f g⟩ : R'.Comparison S' f)
  have a : @homotopyMappingWeakEquivalences C _ M _ _ Z _ _ f ↔
      weakEquivalences SSet.{v} (@CosimplicialResolution.Comparison.precomp C _ M _ _ X R Y S f g Z) := by
    letI := M
    letI := hM
    exact homotopyMappingWeakEquivalences_iff Z g
  have b : @homotopyMappingWeakEquivalences C _ N _ _ Z _ _ f ↔
      weakEquivalences SSet.{v} (@CosimplicialResolution.Comparison.precomp C _ N _ _ X R' Y S' f g' Z) := by
    letI := N
    letI := hN
    exact homotopyMappingWeakEquivalences_iff Z g'
  exact a.trans b.symm

end

end DaggerModels.PartII
