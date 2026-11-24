import DaggerModelsPartII.JTOrdinaryEndpointFibration
import DaggerModelsPartII.StrictFrameMappingWeak

/-!
# Weak invariance of the ordinary JT mapping frame

The groupoid-completed simplex is a Reedy cofibrant ordinary Joyal
parameter. Its tensor with any fixed simplicial set is again a Reedy
cofibrant frame. The strict mapping-space comparison of a Joyal weak
map is therefore a Kan weak equivalence for every quasicategory target.
This reuses the short parameter argument of `JTOrdinaryEndpointFibration`;
the relative Arrow argument there is specific to endpoints and is not used.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open MonoidalCategory DaggerModels

namespace DaggerModels.PartII.OrdinaryJTMappingFrameWeak

noncomputable section

private def ordinaryJoyalModel : ModelCategory SSet.{0} :=
  DaggerActualDCHRightInducedAndMainTheoremD.ordinaryJoyalModel.{0}

private local instance : ModelCategory SSet.{0} := ordinaryJoyalModel
private local instance : CategoryWithWeakEquivalences SSet.{0} :=
  ordinaryJoyalModel.categoryWithWeakEquivalences
private local instance : ModelCategory SSet.{0}ᵒᵖ := inferInstance
private local instance : CategoryWithWeakEquivalences SSet.{0}ᵒᵖ :=
  (inferInstance : ModelCategory SSet.{0}ᵒᵖ).categoryWithWeakEquivalences
private local instance : ModelCategory (SimplexCategoryᵒᵖ ⥤ SSet.{0}ᵒᵖ) :=
  simplicialReedyModelCategory SSet.{0}ᵒᵖ

private local instance (A : SSet.{0}) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft A) :=
  (ihom.adjunction A).leftAdjoint_preservesColimits

private local instance (A : SSet.{0}) :
    PreservesLimitsOfSize.{0, 0} (tensorLeft A).op :=
  preservesLimitsOfSize_op (tensorLeft A)

/-- The literal ordinary JT cosimplicial weight `A × J[•]`. -/
def frame (A : SSet.{0}) : SimplexCategory ⥤ SSet.{0} :=
  GroupoidSimplex.parameter ⋙ tensorLeft A

/-- Naturality in the ordinary horizontal simplicial-set coefficient. -/
def frameMap {A B : SSet.{0}} (u : A ⟶ B) : frame A ⟶ frame B where
  app k := u ▷ GroupoidSimplex.parameter.obj k
  naturality {_ _} f := by
    exact (MonoidalCategory.whisker_exchange u (GroupoidSimplex.parameter.map f)).symm

private theorem parameter_op_isFibrant : IsFibrant GroupoidSimplex.parameter.op := by
  apply (reedyFibrant_iff_matchingComparison _).mpr
  intro n
  apply ((fibrations SSet.{0}ᵒᵖ).cancel_right_of_respectsIso
    ((matchingComparison n).app GroupoidSimplex.parameter.op)
    (JTXiOrdinaryLatching.parameterMatchingIso n).hom).mp
  rw [JTXiOrdinaryLatching.parameterMatchingIso_comp, fibrations_op]
  change
    (DaggerNativeOriginalJoyalSmithModelData.modelData.model).categoryWithCofibrations.cofibrations
      (JTParameterLatchingMono.faceLatchingMap n)
  rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelCof,
    DaggerNativeFullWeakSmithGenerators.boundary_cof]
  exact JTParameterLatchingMono.faceLatchingMap_mono n

private theorem tensor_op_preservesFibrations (A : SSet.{0})
    {K L : SSet.{0}ᵒᵖ} (f : K ⟶ L)
    (hf : fibrations SSet.{0}ᵒᵖ f) :
    fibrations SSet.{0}ᵒᵖ ((tensorLeft A).op.map f) := by
  rw [fibrations_op] at hf ⊢
  change cofibrations SSet.{0} f.unop at hf
  have hm : Mono f.unop := by
    change ordinaryJoyalModel.categoryWithCofibrations.cofibrations f.unop at hf
    rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelCof,
      DaggerNativeFullWeakSmithGenerators.boundary_cof] at hf
    exact hf
  letI : Mono f.unop := hm
  have hA : Mono (A ◁ f.unop) :=
    DaggerNativeIhomRelativeSectionsWeak.left_tensor_mono A f.unop
  change
    (DaggerNativeOriginalJoyalSmithModelData.modelData.model).categoryWithCofibrations.cofibrations
      (A ◁ f.unop)
  rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelCof,
    DaggerNativeFullWeakSmithGenerators.boundary_cof]
  exact hA

/-- Every ordinary JT tensor weight is Reedy cofibrant in the original
Joyal model, expressed as fibrancy of its opposite frame. -/
theorem frame_op_isFibrant (A : SSet.{0}) : IsFibrant (frame A).op := by
  letI : IsFibrant GroupoidSimplex.parameter.op := parameter_op_isFibrant
  change IsFibrant (GroupoidSimplex.parameter.op ⋙ (tensorLeft A).op)
  exact reedyFibrant_comp GroupoidSimplex.parameter.op (tensorLeft A).op
    (tensor_op_preservesFibrations A)

private theorem isFibrant_of_quasicategory (X : SSet.{0})
    [X.Quasicategory] : IsFibrant X := by
  apply (isFibrant_iff_of_isTerminal (terminal.from X)
    (terminalIsTerminal : IsTerminal (⊤_ SSet.{0}))).mpr
  rw [fibration_iff]
  change ordinaryJoyalModel.categoryWithFibrations.fibrations (terminal.from X)
  rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelFib,
    DaggerNativeFullWeakSmithGenerators.boundary_cof]
  exact DaggerNativeJoyalWeakTrivialFibrationSpan.terminal_candidate X

/-- The ordinary JT mapping simplicial set with horizontal coefficient `A`. -/
def mapping (X A : SSet.{0}) : SSet.{0} :=
  (StrictFrameMappingWeak.strictMapping X).obj (frame A).op

/-- Restriction along the literal horizontal map, retaining all `J[k]` parameters. -/
def restriction (X : SSet.{0}) {A B : SSet.{0}} (u : A ⟶ B) :
    mapping X B ⟶ mapping X A :=
  (StrictFrameMappingWeak.strictMapping X).map (NatTrans.op (frameMap u))

/-- Original Joyal weak maps induce Kan weak equivalences of the actual
ordinary JT mapping simplicial sets into any quasicategory. -/
theorem restriction_weak (X : SSet.{0}) [X.Quasicategory]
    {A B : SSet.{0}} (u : A ⟶ B)
    (hu : DaggerNativeJoyalMappingTest.weakCategoricalEquivalences u) :
    DaggerSSetGluing.GW (restriction X u) := by
  letI : IsFibrant X := isFibrant_of_quasicategory X
  letI : IsFibrant (frame A).op := frame_op_isFibrant A
  letI : IsFibrant (frame B).op := frame_op_isFibrant B
  have hg : weakEquivalences (SimplexCategoryᵒᵖ ⥤ SSet.{0}ᵒᵖ)
      (NatTrans.op (frameMap u)) := by
    change simplicialReedyWeakEquivalences SSet.{0}ᵒᵖ (NatTrans.op (frameMap u))
    intro k
    rw [weakEquivalences_op]
    change ordinaryJoyalModel.categoryWithWeakEquivalences.weakEquivalences
      (u ▷ GroupoidSimplex.parameter.obj k.unop)
    rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelWeak]
    exact DaggerNativeJoyalMappingTensor.weak_whiskerRight u hu
      (GroupoidSimplex.parameter.obj k.unop)
  have hKan := StrictFrameMappingWeak.strictMapping_map_weak
    X (NatTrans.op (frameMap u)) hg
  letI : CategoryWithWeakEquivalences SSet.{0} :=
    SSet.modelCategoryQuillen.instCategoryWithWeakEquivalences_topCatModelCategory
  exact (DaggerSSetGluing.weakEquivalence_iff_GW _).mp
    ((weakEquivalence_iff _).mpr hKan)

#print axioms frame_op_isFibrant
#print axioms restriction_weak

end

end DaggerModels.PartII.OrdinaryJTMappingFrameWeak
