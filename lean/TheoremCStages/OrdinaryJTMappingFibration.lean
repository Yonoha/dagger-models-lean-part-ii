import OrdinaryJTRelativeMappingFrame
import OrdinaryJTMappingFrameWeak
import DaggerModelsPartII.StrictFrameMappingFibration

/-!
# Kan fibration of ordinary JT mapping restriction

For a monomorphism of horizontal simplicial-set coefficients, the literal
ordinary JT restriction is a Kan fibration into every quasicategory. If the
coefficient map is also an original Joyal weak equivalence, the restriction
is a Kan trivial fibration. The relative Reedy calculation is supplied by
`OrdinaryJTRelativeMappingFrame`.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open MonoidalCategory DaggerModels

namespace DaggerModels.PartII.OrdinaryJTMappingFibration

open OrdinaryJTMappingFrameWeak

noncomputable section

section OriginalCoefficient

private def ordinaryJoyalModel : ModelCategory SSet.{0} :=
  DaggerActualDCHRightInducedAndMainTheoremD.ordinaryJoyalModel.{0}

private local instance : ModelCategory SSet.{0} := ordinaryJoyalModel
private local instance : CategoryWithWeakEquivalences SSet.{0} :=
  ordinaryJoyalModel.categoryWithWeakEquivalences
private local instance : ModelCategory SSet.{0}ᵒᵖ := inferInstance
private local instance : CategoryWithWeakEquivalences SSet.{0}ᵒᵖ :=
  (inferInstance : ModelCategory SSet.{0}ᵒᵖ).categoryWithWeakEquivalences

private theorem isFibrant_of_quasicategory (X : SSet.{0})
    [X.Quasicategory] : IsFibrant X := by
  apply (isFibrant_iff_of_isTerminal (terminal.from X)
    (terminalIsTerminal : IsTerminal (⊤_ SSet.{0}))).mpr
  rw [fibration_iff]
  change ordinaryJoyalModel.categoryWithFibrations.fibrations (terminal.from X)
  rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelFib,
    DaggerNativeFullWeakSmithGenerators.boundary_cof]
  exact DaggerNativeJoyalWeakTrivialFibrationSpan.terminal_candidate X

private theorem frame_op_maps_weak (A : SSet.{0})
    {s t : SimplexCategoryᵒᵖ} (g : s ⟶ t) :
    weakEquivalences SSet.{0}ᵒᵖ ((frame A).op.map g) := by
  rw [weakEquivalences_op]
  change ordinaryJoyalModel.categoryWithWeakEquivalences.weakEquivalences
    (A ◁ GroupoidSimplex.parameter.map g.unop)
  rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelWeak]
  exact DaggerNativeJoyalMappingTensor.weak_whiskerLeft A
    (GroupoidSimplex.parameter.map g.unop)
    (JTOrdinaryEndpointFibration.parameter_map_weak g.unop)

end OriginalCoefficient

open scoped SSet.modelCategoryQuillen

/-- A monomorphism of horizontal coefficients induces a Kan fibration of
the actual ordinary JT mapping simplicial sets. -/
theorem restriction_fibration (X : SSet.{0}) [X.Quasicategory]
    {A B : SSet.{0}} (u : A ⟶ B) [Mono u] :
    Fibration (restriction X u) := by
  letI : ModelCategory SSet.{0} := ordinaryJoyalModel
  letI : CategoryWithCofibrations SSet.{0} :=
    ordinaryJoyalModel.categoryWithCofibrations
  letI : CategoryWithFibrations SSet.{0} :=
    ordinaryJoyalModel.categoryWithFibrations
  letI : CategoryWithWeakEquivalences SSet.{0} :=
    ordinaryJoyalModel.categoryWithWeakEquivalences
  letI : ModelCategory SSet.{0}ᵒᵖ := inferInstance
  letI : CategoryWithFibrations SSet.{0}ᵒᵖ :=
    (inferInstance : ModelCategory SSet.{0}ᵒᵖ).categoryWithFibrations
  letI : CategoryWithWeakEquivalences SSet.{0}ᵒᵖ :=
    (inferInstance : ModelCategory SSet.{0}ᵒᵖ).categoryWithWeakEquivalences
  letI : ModelCategory (SimplexCategoryᵒᵖ ⥤ SSet.{0}ᵒᵖ) :=
    simplicialReedyModelCategory SSet.{0}ᵒᵖ
  letI : IsFibrant X := isFibrant_of_quasicategory X
  letI : IsFibrant (frame A).op := frame_op_isFibrant A
  letI : IsFibrant (frame B).op := frame_op_isFibrant B
  have hrel : reedyMatchingProperty (fibrations SSet.{0}ᵒᵖ)
      (NatTrans.op (frameMap u)) := by
    intro n
    rw [fibrations_op]
    exact OrdinaryJTRelativeMappingFrame.frameMap_relativeCofibration u n
  have hstrict := StrictFrameMappingFibration.strictMapping_map_fibration X
    (D := (frame B).op) (E := (frame A).op)
    (fun g ↦ frame_op_maps_weak B g)
    (fun g ↦ frame_op_maps_weak A g)
    (NatTrans.op (frameMap u)) hrel
  letI : CategoryWithFibrations SSet.{0} :=
    SSet.modelCategoryQuillen.instCategoryWithFibrations
  change Fibration ((StrictFrameMappingWeak.strictMapping X).map
    (NatTrans.op (frameMap u)))
  exact hstrict

/-- A monomorphic original Joyal weak map gives a Kan trivial fibration
of the actual ordinary JT mapping simplicial sets. -/
theorem restriction_trivialFibration (X : SSet.{0}) [X.Quasicategory]
    {A B : SSet.{0}} (u : A ⟶ B) [Mono u]
    (hu : DaggerNativeJoyalMappingTest.weakCategoricalEquivalences u) :
    trivialFibrations SSet.{0} (restriction X u) := by
  have hf : Fibration (restriction X u) := restriction_fibration X u
  have hw : WeakEquivalence (restriction X u) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr (restriction_weak X u hu)
  exact ⟨(fibration_iff _).mp hf, (weakEquivalence_iff _).mp hw⟩

#print axioms restriction_fibration
#print axioms restriction_trivialFibration

end

end DaggerModels.PartII.OrdinaryJTMappingFibration
