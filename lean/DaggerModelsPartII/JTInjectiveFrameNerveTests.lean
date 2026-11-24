import DaggerModelsPartII.JTSegalFrameLocality
import DaggerModelsPartII.ProjectiveInjectiveComparison
import DaggerModelsPartII.InjectiveStandardFrame

/-!
# Injective-local tests supplied by the actual frame nerve

An original Bergner-fibrant target has an actual frame nerve that is
projectively local. Its injectively fibrant replacement is an injective-local
test object. Every weak equivalence in the specified injective Segal model
passes the derived and strict mapping tests into this replacement.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra MorphismProperty DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTInjectiveFrameNerveTests

open SegalLocalizers JTFrameAdjunction

noncomputable section

private local instance : ModelCategory DaggerSimplicialCat.{0, 0} :=
  DaggerActualRigidificationQuillen.modelG.{0}

/-- A chosen injective-local test target for the literal frame nerve. -/
structure FrameNerveTest (C : DaggerSimplicialCat.{0, 0}) where
  target : ReverseDaggerSpace.{0}
  map : frameNerve.obj C ⟶ target
  rowwiseWeak :
    (ProjectiveKanDiagram.modelCategory
      ReverseSimplexᵒᵖ).categoryWithWeakEquivalences.weakEquivalences map
  localObject :
    (letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
     Localization.localObject localizingFamily target)

/-- An original fibrant frame nerve has an injectively local replacement
along an actual rowwise Kan weak equivalence. -/
theorem exists_frameNerveTest (C : DaggerSimplicialCat.{0, 0}) [IsFibrant C] :
    Nonempty (FrameNerveTest C) := by
  letI : ModelCategory ReverseDaggerSpace.{0} :=
    ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
  have hframe : IsFibrant (frameNerve.obj C) :=
    JTSegalFrameLocality.frameNerve_obj_isFibrant C
  obtain ⟨Z, q, hq, hZ⟩ :=
    (ProjectiveInjectiveComparison.localObject_iff_exists_injectiveLocal
      ReverseSimplexᵒᵖ segalLocalizingFamily (frameNerve.obj C) hframe).mp
      (JTSegalFrameLocality.frameNerve_literal_localObject C)
  refine ⟨⟨Z, q, hq, ?_⟩⟩
  simpa only [segalLocalizingFamily] using hZ

/-- Make the replacement choice once, without changing its actual source map. -/
def frameNerveTest (C : DaggerSimplicialCat.{0, 0}) [IsFibrant C] :
    FrameNerveTest C :=
  Classical.choice (exists_frameNerveTest C)

/-- The selected replacement is fibrant in the specified injective Segal model. -/
theorem frameNerveTest_target_fibrant (C : DaggerSimplicialCat.{0, 0})
    [IsFibrant C] :
    @IsFibrant ReverseDaggerSpace.{0} _
      injectiveSegalModel.categoryWithFibrations _ (frameNerveTest C).target := by
  have hstrict := (injectiveLocalObject_iff_strict (frameNerveTest C).target).mp
    (frameNerveTest C).localObject
  exact (injectiveSegalModel_isFibrant_iff (frameNerveTest C).target).2 hstrict

/-- Every actual injective Segal weak equivalence passes the derived mapping
test into the selected injective-local replacement of a fibrant frame nerve. -/
theorem weak_mappingTest (C : DaggerSimplicialCat.{0, 0}) [IsFibrant C]
    {X Y : ReverseDaggerSpace.{0}} (f : X ⟶ Y)
    (hf : injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences f) :
    (letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
     homotopyMappingWeakEquivalences (frameNerveTest C).target f) := by
  letI : ModelCategory ReverseDaggerSpace.{0} :=
    InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
  have hlocal : Localization.localEquivalences localizingFamily f := by
    change (InjectiveKanDiagram.localizedModelCategory
      ReverseSimplexᵒᵖ LocalizerIndex localizerArrow
      localizerArrow_mono).categoryWithWeakEquivalences.weakEquivalences f at hf
    rw [(InjectiveKanDiagram.localized_exactClasses ReverseSimplexᵒᵖ
      LocalizerIndex localizerArrow localizerArrow_mono).2,
      localizerArrow_family] at hf
    exact hf
  exact hlocal (frameNerveTest C).target (frameNerveTest C).localObject

/-- The same forward test is a literal Kan weak equivalence of strict diagram
mapping simplicial sets, since the selected target is injectively fibrant. -/
theorem weak_strictMappingTest (C : DaggerSimplicialCat.{0, 0}) [IsFibrant C]
    {X Y : ReverseDaggerSpace.{0}} (f : X ⟶ Y)
    (hf : injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences f) :
    weakEquivalences SSet.{0}
      (diagramMappingPrecomp f (frameNerveTest C).target) := by
  letI : ModelCategory ReverseDaggerSpace.{0} :=
    InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
  letI : Fact (InjectiveKanDiagram.GeneratorsAreAllMonos ReverseSimplexᵒᵖ) :=
    ⟨InjectiveKanDiagram.generatorsAreAllMonos ReverseSimplexᵒᵖ⟩
  letI : IsFibrant (frameNerveTest C).target := (frameNerveTest C).localObject.1
  exact (InjectiveKanDiagram.homotopyMappingWeakEquivalences_iff_strict
    ReverseSimplexᵒᵖ f).mp (weak_mappingTest C f hf)

end

end DaggerModels.PartII.JTInjectiveFrameNerveTests
