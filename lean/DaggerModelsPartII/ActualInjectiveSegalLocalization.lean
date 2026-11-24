import DaggerModelsPartII.ActualSegalLocalization

/-!
# Injective Segal localization on the actual Part I index

This uses precisely the same left Kan image family as the projective localization.
The identity is a Quillen equivalence between these two actual-index models.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra
open DaggerModels.PartII.SegalLocalizers
open DaggerModels.PartII.DaggerSimplexPartIIndex
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.ActualIndexProjectiveModel

noncomputable section

/-- The injective localization at the actual left Kan images of the fixed resolutions. -/
def actualInjectiveSegalModel : ModelCategory ActualSpace :=
  InjectiveKanDiagram.localizedModelCategory ActualDaggerSimplexᵒᵖ LocalizerIndex
    actualImageLocalizer actualImageLocalizer_mono

/-- The actual-index injective Segal localization is combinatorial. -/
theorem actualInjectiveSegalModel_combinatorial :
    ModelProperties.combinatorial.{0} actualInjectiveSegalModel :=
  ModelProperties.combinatorial_of_smithData _
    (InjectiveKanDiagram.localizedCombinatorialData ActualDaggerSimplexᵒᵖ LocalizerIndex
      actualImageLocalizer actualImageLocalizer_mono)

/-- Left properness of the actual-index injective localization. -/
theorem actualInjectiveSegalModel_leftProper
    {A B D P : ActualSpace} {i : A ⟶ B} {k : A ⟶ D}
    {l : B ⟶ P} {r : D ⟶ P} (sq : CategoryTheory.IsPushout i k l r)
    (hi : actualInjectiveSegalModel.categoryWithCofibrations.cofibrations i)
    (hk : actualInjectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences k) :
    actualInjectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences l :=
  InjectiveKanDiagram.localized_leftProper ActualDaggerSimplexᵒᵖ LocalizerIndex
    actualImageLocalizer actualImageLocalizer_mono sq hi hk

/-- The localized projective and injective actual-index models have identical weak classes. -/
theorem actualSegalModels_weakEquivalences_eq :
    actualSegalModel.categoryWithWeakEquivalences.weakEquivalences =
      actualInjectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences := by
  have hp := ProjectiveKanDiagram.localized_exactClasses ActualDaggerSimplexᵒᵖ LocalizerIndex
    actualImageLocalizer actualImageLocalizer_mono
  have hi := InjectiveKanDiagram.localized_exactClasses ActualDaggerSimplexᵒᵖ LocalizerIndex
    actualImageLocalizer actualImageLocalizer_mono
  exact hp.2.trans ((ProjectiveInjectiveComparison.localEquivalences_eq _ _).trans hi.2.symm)

/-- The actual-index identity is the localized projective-to-injective Quillen equivalence. -/
theorem actualSegalIdentity_isQuillenEquivalence :
    @Adjunction.IsQuillenEquivalence ActualSpace ActualSpace _ _
      actualSegalModel actualInjectiveSegalModel (𝟭 _) (𝟭 _) Adjunction.id :=
  localizedIdentity_isQuillenEquivalence ActualDaggerSimplexᵒᵖ LocalizerIndex
    actualImageLocalizer actualImageLocalizer_mono

/-- Pushout-product SM7 for the actual-index injective Segal localization. -/
theorem actualInjectiveSegalModel_pushoutProduct_sm7
    {A B : ActualSpace} (i : A ⟶ B) {K L : SSet.{0}} (j : K ⟶ L)
    (hi : actualInjectiveSegalModel.categoryWithCofibrations.cofibrations i)
    (hj : HomotopicalAlgebra.cofibrations SSet.{0} j)
    (sq : Functor.PushoutObjObj
      (InjectiveKanDiagram.curriedDiagramTensor ActualDaggerSimplexᵒᵖ) i j) :
    actualInjectiveSegalModel.categoryWithCofibrations.cofibrations sq.ι ∧
      ((actualInjectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences i ∨
          HomotopicalAlgebra.weakEquivalences SSet.{0} j) →
        actualInjectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences sq.ι) :=
  InjectiveKanDiagram.localized_pushoutProduct_sm7 ActualDaggerSimplexᵒᵖ LocalizerIndex
    actualImageLocalizer actualImageLocalizer_mono i j hi hj sq

end

end DaggerModels.PartII.ActualIndexProjectiveModel
