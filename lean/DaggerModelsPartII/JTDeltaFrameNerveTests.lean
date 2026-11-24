import DaggerModelsPartII.JTInjectiveFrameNerveTests
import DaggerModelsPartII.JTCofibrantAugmentationWeak
import DaggerModelsPartII.ConstantVertexQuillenFromLocalWeak

/-!
# Constant-vertex images in the frame-nerve tests

The original frame realization of a projective arrow resolution gives the
mapping test into the actual frame nerve. The chosen rowwise weak comparison
then transfers it to the injectively fibrant test target.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTDeltaFrameNerveTests

open ConstantVertexAdjunction JTInjectiveFrameNerveTests SegalLocalizers

noncomputable section

private local instance : HasLimits DaggerSimplicialCat.{0, 0} := daggerSimplicialCatHasLimits
private local instance : HasColimits DaggerSimplicialCat.{0, 0} := daggerSimplicialCatHasColimits
private local instance : ModelCategory DaggerSimplicialCat.{0, 0} :=
  DaggerActualRigidificationQuillen.modelG.{0}

section ProjectiveTests

private local instance : ModelCategory ReverseDaggerSpace.{0} :=
  ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ

/-- The constant-vertex image of an original weak equivalence passes the
derived projective mapping test into the original frame nerve. -/
theorem deltaMap_frameNerve_mappingTest
    {X Y : DaggerSSet.{0}} (f : X ⟶ Y)
    (hf : DaggerJoyalWeakProperties.standardJoyalWeakEquivalences f)
    (C : DaggerSimplicialCat.{0, 0}) [IsFibrant C] :
    homotopyMappingWeakEquivalences (JTFrameAdjunction.frameNerve.obj C) (delta.map f) := by
  let R := cofibrantArrowResolution (delta.map f)
  letI : IsCofibrant R.source := R.source_cofibrant
  letI : IsCofibrant R.target := R.target_cofibrant
  letI : IsFibrant (JTFrameAdjunction.frameNerve.obj C) :=
    JTSegalFrameLocality.frameNerve_obj_isFibrant C
  letI : JTFrameAdjunction.adjunction.IsQuillenAdjunction := JTFrameQuillen.isQuillenAdjunction
  apply (R.homotopyMappingWeakEquivalences_iff _).mp
  apply (homotopyMappingWeakEquivalences_leftQuillen_iff JTFrameAdjunction.adjunction R.hom C).mp
  exact weakEquivalences_le_homotopyMappingWeakEquivalences C _
    (JTCofibrantAugmentationWeak.frameRealization_resolution_weak f hf R)

/-- The same constant-vertex image passes the strict Kan mapping test into
the chosen injectively fibrant frame-nerve replacement. -/
theorem deltaMap_weak_strictMappingTest
    {X Y : DaggerSSet.{0}} (f : X ⟶ Y)
    (hf : DaggerJoyalWeakProperties.standardJoyalWeakEquivalences f)
    (C : DaggerSimplicialCat.{0, 0}) [IsFibrant C] :
    weakEquivalences SSet.{0}
      (diagramMappingPrecomp (delta.map f) (frameNerveTest C).target) := by
  let T := frameNerveTest C
  letI : IsFibrant (JTFrameAdjunction.frameNerve.obj C) :=
    JTSegalFrameLocality.frameNerve_obj_isFibrant C
  letI : IsFibrant T.target :=
    ProjectiveInjectiveComparison.isFibrant_projective ReverseSimplexᵒᵖ T.target T.localObject.1
  have hprojective : homotopyMappingWeakEquivalences T.target (delta.map f) :=
    (homotopyMappingWeakEquivalences_target_iff T.map T.rowwiseWeak (delta.map f)).mp
      (deltaMap_frameNerve_mappingTest f hf C)
  letI : ModelCategory ReverseDaggerSpace.{0} :=
    InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
  letI : IsFibrant T.target := T.localObject.1
  letI : Fact (InjectiveKanDiagram.GeneratorsAreAllMonos ReverseSimplexᵒᵖ) :=
    ⟨InjectiveKanDiagram.generatorsAreAllMonos ReverseSimplexᵒᵖ⟩
  exact (InjectiveKanDiagram.homotopyMappingWeakEquivalences_iff_strict
    ReverseSimplexᵒᵖ (delta.map f)).mp
      ((ProjectiveInjectiveComparison.homotopyMapping_iff
        ReverseSimplexᵒᵖ T.target T.localObject.1 (delta.map f)).mp hprojective)

end ProjectiveTests

private local instance : ModelCategory DaggerSSet.{0} :=
  DaggerOriginalJoyalModel.standardModelCategory.{0}
private local instance : ModelCategory ReverseDaggerSpace.{0} := injectiveSegalModel

/-- Detection by the chosen frame-nerve tests gives the Quillen adjunction of
the original constant-vertex functor and vertex evaluation. -/
theorem isQuillenAdjunction_of_frameNerveTests_detect_weak
    (hdetect : ∀ ⦃A B : ReverseDaggerSpace.{0}⦄ (g : A ⟶ B),
      (∀ (C : DaggerSimplicialCat.{0, 0}) [IsFibrant C],
        weakEquivalences SSet.{0} (diagramMappingPrecomp g (frameNerveTest C).target)) →
      weakEquivalences ReverseDaggerSpace.{0} g) :
    ConstantVertexAdjunction.adjunction.IsQuillenAdjunction := by
  apply isQuillenAdjunction_of_cofibrant_weak
  intro X Y f _ _ hf
  apply hdetect (delta.map f)
  intro C hC
  have hf' : DaggerJoyalWeakProperties.standardJoyalWeakEquivalences f := by
    rwa [← DaggerOriginalJoyalModel.standard_model_weak]
  exact deltaMap_weak_strictMappingTest f hf' C

end

end DaggerModels.PartII.JTDeltaFrameNerveTests
