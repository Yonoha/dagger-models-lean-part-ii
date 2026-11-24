import DaggerModelsPartII.SegalLocalizationModels
import DaggerModelsPartII.ActualIndexProjectiveModel

/-!
# Segal localization on the actual Part I dagger-simplex index

The localizing family consists of the actual left Kan images of the fixed
functorial projective resolutions of the reversal Segal maps. Fibrancy is
levelwise Kan fibrancy together with derived Segal completeness after restriction.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra MorphismProperty
open DaggerModels.PartII.SegalLocalizers
open DaggerModels.PartII.DaggerSimplexPartIIndex
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.ActualIndexProjectiveModel

noncomputable section

local instance actualLocalizationBaseModel : ModelCategory ActualSpace := modelCategory
local instance reversalLocalizationBaseModel : ModelCategory ReverseDaggerSpace.{0} :=
  ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ

/-- The literal left Kan image of the chosen resolution of a reversal localizer. -/
def actualImageLocalizer (i : LocalizerIndex) : Arrow ActualSpace :=
  Arrow.mk (actualLeftExtension.{0}.map (functorialProjectiveResolution i).hom)

/-- Left Kan images of these projective cofibrations are monomorphisms. -/
theorem actualImageLocalizer_mono (i : LocalizerIndex) : Mono (actualImageLocalizer i).hom := by
  letI : actualLeftAdjunction.{0}.IsQuillenAdjunction :=
    actualLeftAdjunction_projective_isQuillen
  letI := (functorialProjectiveResolution i).cofibration
  have ht : Cofibration (actualImageLocalizer i).hom := by
    change Cofibration (actualLeftExtension.{0}.map (functorialProjectiveResolution i).hom)
    letI : actualLeftExtension.{0}.PreservesCofibrations :=
      Adjunction.IsQuillenAdjunction.preservesCofibrations actualLeftAdjunction.{0}
    infer_instance
  have hf : (ProjectiveKanDiagram.boundaryGenerators ActualDaggerSimplexᵒᵖ).rlp.llp
      (actualImageLocalizer i).hom := (cofibration_iff _).mp ht
  exact (NatTrans.mono_iff_mono_app _).mpr
    (ProjectiveKanDiagram.boundaryCofibrations_levelwiseMono _ _ hf)

/-- The arrow-indexed family is the actual left Kan image family already specified. -/
theorem actualImageLocalizer_family :
    InjectiveKanDiagram.diagramLocalizingFamily ActualDaggerSimplexᵒᵖ LocalizerIndex
      actualImageLocalizer = functorialImageSRev actualU := rfl

/-- The projective localization on the manuscript's actual free dagger simplices. -/
def actualSegalModel : ModelCategory ActualSpace :=
  ProjectiveKanDiagram.localizedModelCategory ActualDaggerSimplexᵒᵖ LocalizerIndex
    actualImageLocalizer actualImageLocalizer_mono

/-- Fibrant actual-index objects are precisely levelwise Kan objects whose
reversal restriction is a complete dagger Segal space in the derived sense. -/
theorem actualSegalModel_isFibrant_iff (W : ActualSpace) :
    @IsFibrant ActualSpace _ actualSegalModel.categoryWithFibrations _ W ↔
      (∀ d, IsFibrant (W.obj d)) ∧
        derivedUnitarilyCompleteSegalCondition (actualRestriction.{0}.obj W) := by
  have hlocal := ProjectiveKanDiagram.localized_isFibrant_iff
    ActualDaggerSimplexᵒᵖ LocalizerIndex actualImageLocalizer actualImageLocalizer_mono W
  have htests := actualProjectiveLocalObjects_iff W
  constructor
  · intro h
    have hh := htests.mp (hlocal.mp h)
    refine ⟨hh.1, ?_⟩
    apply (projectiveLocalObject_iff_derived _).mp
    refine ⟨?_, hh.2⟩
    exact (ProjectiveKanDiagram.model_isFibrant_iff ReverseSimplexᵒᵖ _).mpr
      (fun d ↦ hh.1 (actualU.op.obj d))
  · rintro ⟨hW, hR⟩
    have hl := (projectiveLocalObject_iff_derived _).mpr hR
    apply hlocal.mpr
    exact htests.mpr ⟨hW, hl.2⟩

/-- The actual-index Segal localization is combinatorial. -/
theorem actualSegalModel_combinatorial :
    ModelProperties.combinatorial.{0} actualSegalModel :=
  ModelProperties.combinatorial_of_smithData _
    (ProjectiveKanDiagram.localizedCombinatorialData ActualDaggerSimplexᵒᵖ LocalizerIndex
      actualImageLocalizer actualImageLocalizer_mono)

/-- The actual-index localization is left proper. -/
theorem actualSegalModel_leftProper
    {A B D P : ActualSpace} {i : A ⟶ B} {k : A ⟶ D}
    {l : B ⟶ P} {r : D ⟶ P} (sq : CategoryTheory.IsPushout i k l r)
    (hi : actualSegalModel.categoryWithCofibrations.cofibrations i)
    (hk : actualSegalModel.categoryWithWeakEquivalences.weakEquivalences k) :
    actualSegalModel.categoryWithWeakEquivalences.weakEquivalences l :=
  ProjectiveKanDiagram.localized_leftProper ActualDaggerSimplexᵒᵖ LocalizerIndex
    actualImageLocalizer actualImageLocalizer_mono sq hi hk

/-- The localized weak class is exactly the derived local class at the actual Kan images. -/
theorem actualSegalModel_weakEquivalences :
    actualSegalModel.categoryWithWeakEquivalences.weakEquivalences =
      Localization.localEquivalences (functorialImageSRev actualU) :=
  (ProjectiveKanDiagram.localized_exactClasses ActualDaggerSimplexᵒᵖ LocalizerIndex
    actualImageLocalizer actualImageLocalizer_mono).2

end

end DaggerModels.PartII.ActualIndexProjectiveModel
