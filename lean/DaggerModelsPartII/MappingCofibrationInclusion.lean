import DaggerModelsPartII.CosimplicialFrameNormalization

/-!
# Derived mapping tests under an inclusion of cofibrations

A resolution for the model with fewer cofibrations is a weakly augmented frame
for the other model. The frame normalization theorem computes both tests on
that same frame.
-/

set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite Simplicial
open scoped SSet.modelCategoryQuillen
universe v u
namespace DaggerModels.PartII
noncomputable section
variable {C : Type u} [Category.{v} C]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]

omit [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C] in
/-- Enlarging cofibrations while keeping weak equivalences shrinks fibrations. -/
theorem fibrations_le_of_cofibrations_le (M N : ModelCategory C)
    (hcof : M.categoryWithCofibrations.cofibrations ≤ N.categoryWithCofibrations.cofibrations)
    (hweak : M.categoryWithWeakEquivalences.weakEquivalences =
      N.categoryWithWeakEquivalences.weakEquivalences) :
    N.categoryWithFibrations.fibrations ≤ M.categoryWithFibrations.fibrations := by
  have hM : M.categoryWithFibrations.fibrations =
      (M.categoryWithCofibrations.cofibrations ⊓
        M.categoryWithWeakEquivalences.weakEquivalences).rlp := by
    letI := M
    exact (rlp_eq_of_wfs (trivialCofibrations C) (fibrations C)).symm
  have hN : N.categoryWithFibrations.fibrations =
      (N.categoryWithCofibrations.cofibrations ⊓
        N.categoryWithWeakEquivalences.weakEquivalences).rlp := by
    letI := N
    exact (rlp_eq_of_wfs (trivialCofibrations C) (fibrations C)).symm
  rw [hM, hN]
  apply antitone_rlp
  intro X Y f hf
  exact ⟨hcof f hf.1, hweak ▸ hf.2⟩

omit [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C] in
/-- Equal weak classes and an inclusion of cofibrations make the identity a Quillen equivalence. -/
theorem identity_isQuillenEquivalence_of_cofibrations_le (M N : ModelCategory C)
    (hcof : M.categoryWithCofibrations.cofibrations ≤ N.categoryWithCofibrations.cofibrations)
    (hweak : M.categoryWithWeakEquivalences.weakEquivalences =
      N.categoryWithWeakEquivalences.weakEquivalences) :
    @Adjunction.IsQuillenEquivalence C C _ _ M N (𝟭 _) (𝟭 _) Adjunction.id := by
  have hL : @Functor.PreservesCofibrations C C _ _ M N (𝟭 _) :=
    (@Functor.preservesCofibrations_iff _ _ _ _ M N (𝟭 _)).mpr hcof
  have hR : @Functor.PreservesFibrations C C _ _ N M (𝟭 _) :=
    (@Functor.preservesFibrations_iff _ _ _ _ N M (𝟭 _)).mpr
      (fibrations_le_of_cofibrations_le M N hcof hweak)
  let hAdj : @Adjunction.IsQuillenAdjunction C C _ _ M N (𝟭 _) (𝟭 _) Adjunction.id :=
    @Adjunction.IsQuillenAdjunction.mk _ _ _ _ M N (𝟭 _) (𝟭 _) Adjunction.id hL hR
  refine @Adjunction.IsQuillenEquivalence.mk _ _ _ _ M N
    (𝟭 _) (𝟭 _) Adjunction.id hAdj ?_
  intro A X hA hX f
  simp only [weakEquivalence_iff, Adjunction.homEquiv_unit]
  change M.categoryWithWeakEquivalences.weakEquivalences (𝟙 A ≫ f) ↔
    N.categoryWithWeakEquivalences.weakEquivalences f
  rw [Category.id_comp, hweak]

/-- On a common fibrant target, equal weak classes and an inclusion of
cofibrations give equal derived mapping tests. -/
theorem homotopyMappingWeakEquivalences_iff_of_cofibrations_le (M N : ModelCategory C)
    (hcof : M.categoryWithCofibrations.cofibrations ≤ N.categoryWithCofibrations.cofibrations)
    (hweak : M.categoryWithWeakEquivalences.weakEquivalences =
      N.categoryWithWeakEquivalences.weakEquivalences) (Z : C)
    (hM : @IsFibrant C _ M.categoryWithFibrations _ Z)
    (hN : @IsFibrant C _ N.categoryWithFibrations _ Z) {X Y : C} (f : X ⟶ Y) :
    @homotopyMappingWeakEquivalences C _ M _ _ Z _ _ f ↔
      @homotopyMappingWeakEquivalences C _ N _ _ Z _ _ f := by
  let R := @cosimplicialResolution C _ M _ _ X
  let S := @cosimplicialResolution C _ M _ _ Y
  let g := @CosimplicialResolution.comparison C _ M _ _ X R Y S f
  let a := @CosimplicialResolution.augmentationOp C _ M _ _ X R
  let b := @CosimplicialResolution.augmentationOp C _ M _ _ Y S
  let comparisonMap := @CosimplicialResolution.Comparison.mapOp C _ M _ _ X R Y S f g
  have hcomm := @CosimplicialResolution.Comparison.comm C _ M _ _ X R Y S f g
  have htestM : @homotopyMappingWeakEquivalences C _ M _ _ Z _ _ f ↔
      weakEquivalences SSet.{v}
        ((CosimplicialResolution.mappingFromOppositeDiagram Z).map comparisonMap) := by
    letI := M
    letI := hM
    exact homotopyMappingWeakEquivalences_iff Z g
  letI := N
  letI : ModelCategory (SimplexCategoryᵒᵖ ⥤ Cᵒᵖ) := simplicialReedyModelCategory Cᵒᵖ
  have frameFibrant : ∀ {A : C} (T : @CosimplicialResolution C _ M _ _ A),
      IsFibrant (@CosimplicialResolution.oppositeDiagram C _ M _ _ A T) := by
    intro A T
    let D := @CosimplicialResolution.oppositeDiagram C _ M _ _ A T
    apply (reedyFibrant_iff_matchingComparison D).mpr
    intro n
    rw [fibrations_op]
    have ht : M.categoryWithCofibrations.cofibrations
        (((matchingComparison n).app D).unop) := by
      letI := M
      letI : ModelCategory (SimplexCategoryᵒᵖ ⥤ Cᵒᵖ) := simplicialReedyModelCategory Cᵒᵖ
      have hf := (reedyFibrant_iff_matchingComparison D).mp
        (@CosimplicialResolution.fibrantOp C _ M _ _ A T) n
      rw [fibrations_op] at hf
      exact hf
    exact hcof _ ht
  have augmentationWeak : ∀ {A : C} (T : @CosimplicialResolution C _ M _ _ A),
      weakEquivalences (SimplexCategoryᵒᵖ ⥤ Cᵒᵖ)
        (@CosimplicialResolution.augmentationOp C _ M _ _ A T) := by
    intro A T n
    change weakEquivalences Cᵒᵖ ((@CosimplicialResolution.augmentationOp C _ M _ _ A T).app n)
    rw [weakEquivalences_op]
    change N.categoryWithWeakEquivalences.weakEquivalences _
    rw [← hweak]
    exact @CosimplicialResolution.augmentation_weak C _ M _ _ A T n
  letI := hN
  letI := frameFibrant R
  letI := frameFibrant S
  have htestN := homotopyMappingWeakEquivalences_iff_of_frames (Z := Z) f
    a b (augmentationWeak R) (augmentationWeak S)
    comparisonMap hcomm
  exact htestM.trans htestN.symm
end
end DaggerModels.PartII
