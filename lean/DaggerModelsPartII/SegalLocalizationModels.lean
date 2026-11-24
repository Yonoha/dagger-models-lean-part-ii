import DaggerModelsPartII.InjectiveLocalizationModel
import DaggerModelsPartII.ProjectiveLocalizationModel
import DaggerModelsPartII.InjectiveSegalLocality
import DaggerModelsPartII.SegalRepresentables
import DaggerModelsPartII.FunctorialSegalLocalizers
import DaggerModelsPartII.DiagramLocalizedIdentity
import DaggerModelsPartII.LocalizedInjectiveSimplicial
import DaggerModelsPartII.CombinatorialModel

/-!
# The reversal-indexed complete Segal localizations

The chosen family is exactly the spine and walking-unitary family from the
manuscript. Its projective and injective localizations have the stated strict
and derived Segal-completeness descriptions of fibrant objects.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.SegalLocalizers

noncomputable section

/-- The literal manuscript family, indexed as arrows for the localization construction. -/
def localizerArrow (i : LocalizerIndex) : Arrow ReverseDaggerSpace.{0} :=
  Arrow.mk (localizerMap.{0} i).2.2

/-- Each literal Segal or completeness map is a monomorphism. -/
theorem localizerArrow_mono (i : LocalizerIndex) : Mono (localizerArrow i).hom :=
  SegalRepresentables.S_rev_mono ⟨i, rfl⟩

/-- The arrow presentation gives exactly the original localizing family. -/
theorem localizerArrow_family :
    InjectiveKanDiagram.diagramLocalizingFamily ReverseSimplexᵒᵖ LocalizerIndex
      localizerArrow = localizingFamily := rfl

/-- The injective localization at the manuscript's Segal and completeness maps. -/
def injectiveSegalModel : ModelCategory ReverseDaggerSpace.{0} :=
  InjectiveKanDiagram.localizedModelCategory ReverseSimplexᵒᵖ LocalizerIndex
    localizerArrow localizerArrow_mono

/-- The projective localization, with the same local weak class as the resolved family. -/
def projectiveSegalModel : ModelCategory ReverseDaggerSpace.{0} :=
  ProjectiveKanDiagram.localizedModelCategory ReverseSimplexᵒᵖ LocalizerIndex
    localizerArrow localizerArrow_mono

/-- Injectively localized fibrant objects are precisely strict complete dagger Segal spaces. -/
theorem injectiveSegalModel_isFibrant_iff (W : ReverseDaggerSpace.{0}) :
    @IsFibrant ReverseDaggerSpace.{0} _ injectiveSegalModel.categoryWithFibrations _ W ↔
      (letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ;
        IsFibrant W ∧ unitarilyCompleteSegalCondition W) := by
  exact (InjectiveKanDiagram.localized_isFibrant_iff ReverseSimplexᵒᵖ LocalizerIndex
    localizerArrow localizerArrow_mono W).trans (injectiveLocalObject_iff_strict W)

/-- Projectively localized fibrant objects are precisely the complete dagger Segal
spaces in the derived sense, including levelwise Kan fibrancy. -/
theorem projectiveSegalModel_isFibrant_iff (W : ReverseDaggerSpace.{0}) :
    @IsFibrant ReverseDaggerSpace.{0} _ projectiveSegalModel.categoryWithFibrations _ W ↔
      derivedUnitarilyCompleteSegalCondition W := by
  exact (ProjectiveKanDiagram.localized_isFibrant_iff ReverseSimplexᵒᵖ LocalizerIndex
    localizerArrow localizerArrow_mono W).trans (projectiveLocalObject_iff_derived W)

/-- The localized projective weak equivalences are exactly those specified by
functorial projective cofibrant resolutions of the manuscript family. -/
theorem projectiveSegalModel_weakEquivalences :
    projectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences =
      (letI := ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ;
        Localization.localEquivalences functorialProjectiveSRev) := by
  have h := (ProjectiveKanDiagram.localized_exactClasses ReverseSimplexᵒᵖ LocalizerIndex
    localizerArrow localizerArrow_mono).2
  exact h.trans functorialProjectiveSRev_localEquivalences.symm

/-- The injective Segal localization is combinatorial with its two exact lifting classes. -/
theorem injectiveSegalModel_combinatorial :
    ModelProperties.combinatorial.{0} injectiveSegalModel :=
  ModelProperties.combinatorial_of_smithData _
    (InjectiveKanDiagram.localizedCombinatorialData ReverseSimplexᵒᵖ LocalizerIndex
      localizerArrow localizerArrow_mono)

/-- The projective Segal localization is combinatorial. -/
theorem projectiveSegalModel_combinatorial :
    ModelProperties.combinatorial.{0} projectiveSegalModel :=
  ModelProperties.combinatorial_of_smithData _
    (ProjectiveKanDiagram.localizedCombinatorialData ReverseSimplexᵒᵖ LocalizerIndex
      localizerArrow localizerArrow_mono)

/-- Left properness of the injective Segal localization. -/
theorem injectiveSegalModel_leftProper
    {A B D P : ReverseDaggerSpace.{0}} {i : A ⟶ B} {k : A ⟶ D}
    {l : B ⟶ P} {r : D ⟶ P} (sq : IsPushout i k l r)
    (hi : injectiveSegalModel.categoryWithCofibrations.cofibrations i)
    (hk : injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences k) :
    injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences l :=
  InjectiveKanDiagram.localized_leftProper ReverseSimplexᵒᵖ LocalizerIndex
    localizerArrow localizerArrow_mono sq hi hk

/-- Left properness of the projective Segal localization. -/
theorem projectiveSegalModel_leftProper
    {A B D P : ReverseDaggerSpace.{0}} {i : A ⟶ B} {k : A ⟶ D}
    {l : B ⟶ P} {r : D ⟶ P} (sq : IsPushout i k l r)
    (hi : projectiveSegalModel.categoryWithCofibrations.cofibrations i)
    (hk : projectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences k) :
    projectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences l :=
  ProjectiveKanDiagram.localized_leftProper ReverseSimplexᵒᵖ LocalizerIndex
    localizerArrow localizerArrow_mono sq hi hk

/-- The identity gives the manuscript's projective-to-injective localized Quillen equivalence. -/
theorem segalIdentity_isQuillenEquivalence :
    @Adjunction.IsQuillenEquivalence ReverseDaggerSpace.{0} ReverseDaggerSpace.{0} _ _
      projectiveSegalModel injectiveSegalModel (𝟭 _) (𝟭 _) Adjunction.id :=
  localizedIdentity_isQuillenEquivalence ReverseSimplexᵒᵖ LocalizerIndex
    localizerArrow localizerArrow_mono

/-- Pushout-product SM7 for the actual injective Segal localization. -/
theorem injectiveSegalModel_pushoutProduct_sm7
    {A B : ReverseDaggerSpace.{0}} (i : A ⟶ B) {K L : SSet.{0}} (j : K ⟶ L)
    (hi : injectiveSegalModel.categoryWithCofibrations.cofibrations i)
    (hj : HomotopicalAlgebra.cofibrations SSet.{0} j)
    (sq : Functor.PushoutObjObj (InjectiveKanDiagram.curriedDiagramTensor ReverseSimplexᵒᵖ) i j) :
    injectiveSegalModel.categoryWithCofibrations.cofibrations sq.ι ∧
      ((injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences i ∨
          HomotopicalAlgebra.weakEquivalences SSet.{0} j) →
        injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences sq.ι) :=
  InjectiveKanDiagram.localized_pushoutProduct_sm7 ReverseSimplexᵒᵖ LocalizerIndex
    localizerArrow localizerArrow_mono i j hi hj sq

end

end DaggerModels.PartII.SegalLocalizers
