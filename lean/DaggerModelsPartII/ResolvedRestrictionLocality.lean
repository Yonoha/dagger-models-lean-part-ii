import DaggerModelsPartII.CofibrantUnit
import DaggerModelsPartII.ActualInjectiveSegalLocalization

/-!
# Restriction of the actual resolved localizers

Every actual left-Kan image of a functorially resolved reversal localizer
restricts to a weak equivalence in the injective Segal localization.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra MorphismProperty DaggerModels
open DaggerModels.PartII.DaggerSimplexPartIIndex

namespace DaggerModels.PartII.ResolvedRestrictionLocality

open SegalLocalizers ActualIndexProjectiveModel CofibrantUnit

noncomputable section

private local instance : ModelCategory ReverseDaggerSpace.{0} :=
  ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ

private theorem reversal_localized_weakEquivalences_eq :
    projectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences =
      injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences := by
  have hp := ProjectiveKanDiagram.localized_exactClasses ReverseSimplexᵒᵖ
    LocalizerIndex localizerArrow localizerArrow_mono
  have hi := InjectiveKanDiagram.localized_exactClasses ReverseSimplexᵒᵖ
    LocalizerIndex localizerArrow localizerArrow_mono
  exact hp.2.trans
    ((ProjectiveInjectiveComparison.localEquivalences_eq _ _).trans hi.2.symm)

private theorem resolved_localizer_localWeak (i : LocalizerIndex) :
    injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
      (functorialProjectiveResolution i).hom := by
  have hmem : functorialProjectiveSRev
      (functorialProjectiveResolution i).hom := MorphismProperty.ofHoms.mk i
  have hlocal : Localization.localEquivalences functorialProjectiveSRev
      (functorialProjectiveResolution i).hom :=
    Localization.family_le_localEquivalences functorialProjectiveSRev _ hmem
  have hp : projectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
      (functorialProjectiveResolution i).hom := by
    rw [projectiveSegalModel_weakEquivalences]
    exact hlocal
  rw [← reversal_localized_weakEquivalences_eq]
  exact hp

/-- Restricting each literal actual left-Kan image of a resolved localizer
gives an injective reversal Segal local weak equivalence. -/
theorem actualRestriction_imageLocalizer_localWeak (i : LocalizerIndex) :
    injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
      ((actualRestriction.{0}).map (actualImageLocalizer i).hom) := by
  let s := (functorialProjectiveResolution i).hom
  have hA := (functorialProjectiveResolution i).source_cofibrant
  have hB := (functorialProjectiveResolution i).target_cofibrant
  have hηA := (actualUnit_trivial_of_projectiveCofibrant
    (functorialProjectiveResolution i).source hA).2
  have hηB := (actualUnit_trivial_of_projectiveCofibrant
    (functorialProjectiveResolution i).target hB).2
  have hs := resolved_localizer_localWeak i
  have hnat := (actualLeftAdjunction.{0}).unit.naturality s
  have hcomp : injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
      (s ≫ (actualLeftAdjunction.{0}).unit.app
        (functorialProjectiveResolution i).target) :=
    injectiveSegalModel.cm2.comp_mem _ _ hs hηB
  change injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
    ((actualLeftExtension.{0} ⋙ actualRestriction.{0}).map s)
  apply injectiveSegalModel.cm2.of_precomp
    ((actualLeftAdjunction.{0}).unit.app
      (functorialProjectiveResolution i).source) _ hηA
  simpa only [Functor.id_map] using hnat.symm ▸ hcomp

end

end DaggerModels.PartII.ResolvedRestrictionLocality
