import DaggerModelsPartII.JTDeltaFrameNerveTests
import DaggerModelsPartII.JTStrictificationCoefficients

/-!
# Frame-nerve detection from the chosen strictification

The two maps of the actual strictification span can be compared in the
unlocalized injective model after applying its explicit local replacement.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra MorphismProperty DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTFrameNerveDetectionFromStrictification

open SegalLocalizers JTInjectiveFrameNerveTests JTStrictificationMaps
open JTStrictificationCoefficients

noncomputable section

private local instance : ModelCategory ReverseDaggerSpace.{0} :=
  InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
private local instance : ModelCategory DaggerSimplicialCat.{0, 0} :=
  DaggerActualRigidificationQuillen.modelG.{0}
private local instance : Fact (InjectiveKanDiagram.GeneratorsAreAllMonos ReverseSimplexᵒᵖ) :=
  ⟨InjectiveKanDiagram.generatorsAreAllMonos ReverseSimplexᵒᵖ⟩

private abbrev localWeak := Localization.localEquivalences localizingFamily

private abbrev replacement :=
  InjectiveKanDiagram.localReplacement ReverseSimplexᵒᵖ LocalizerIndex localizerArrow

private abbrev replacementUnit :=
  InjectiveKanDiagram.localReplacementUnit ReverseSimplexᵒᵖ LocalizerIndex localizerArrow

private theorem replacement_local (Z : ReverseDaggerSpace.{0}) :
    Localization.localObject localizingFamily (replacement.obj Z) :=
  InjectiveKanDiagram.localReplacement_isLocal ReverseSimplexᵒᵖ LocalizerIndex
    localizerArrow localizerArrow_mono Z

private theorem localWeak_eq : localWeak =
    injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences :=
  (InjectiveKanDiagram.localized_exactClasses ReverseSimplexᵒᵖ
    LocalizerIndex localizerArrow localizerArrow_mono).2.symm

private theorem replacement_map_weak {Z T : ReverseDaggerSpace.{0}} (f : Z ⟶ T)
    (hf : localWeak f) : weakEquivalences ReverseDaggerSpace.{0} (replacement.map f) := by
  have h := InjectiveKanDiagram.localEquivalences_eq_inverseImage ReverseSimplexᵒᵖ
    LocalizerIndex localizerArrow localizerArrow_mono
  change localWeak = (weakEquivalences ReverseDaggerSpace.{0}).inverseImage replacement at h
  rw [h] at hf
  exact hf

private theorem replacementUnit_weak_of_local {Z : ReverseDaggerSpace.{0}}
    (hZ : Localization.localObject localizingFamily Z) :
    weakEquivalences ReverseDaggerSpace.{0} (replacementUnit.app Z) :=
  (Localization.localEquivalence_iff_weak_of_local localizingFamily (replacementUnit.app Z)
    hZ (replacement_local Z)).mp
      (InjectiveKanDiagram.localReplacementUnit_localEquivalence ReverseSimplexᵒᵖ
        LocalizerIndex localizerArrow localizerArrow_mono Z)

/-- Weakness of the manuscript's chosen strictification on injective-local
objects suffices for detection by the chosen frame-nerve tests. -/
theorem detect_weak_of_chosenPsi
    (hpsi : ∀ Z, Localization.localObject localizingFamily Z →
      injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences (chosenPsi Z))
    {A B : ReverseDaggerSpace.{0}} (f : A ⟶ B)
    (hf : ∀ (C : DaggerSimplicialCat.{0, 0}) [IsFibrant C],
      weakEquivalences SSet.{0} (diagramMappingPrecomp f (frameNerveTest C).target)) :
    injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences f := by
  rw [← localWeak_eq]
  intro Z hZ
  let C := rigidCoefficient (chosenT Z)
  letI : IsFibrant C := rigidCoefficient_fibrant (chosenT Z)
  let T := frameNerveTest C
  let g : Qproj.obj Z ⟶ T.target := chosenPsi Z ≫ T.map
  have hp : localWeak (p.app Z) := by
    apply Localization.weakEquivalences_le_localEquivalences localizingFamily
    change (InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ).categoryWithWeakEquivalences.weakEquivalences
      (p.app Z)
    rw [← ProjectiveInjectiveComparison.weakEquivalences_eq ReverseSimplexᵒᵖ]
    exact (p_trivialFibration Z).2
  have hg : localWeak g := by
    have hψ : localWeak (chosenPsi Z) := by
      rw [localWeak_eq]
      exact hpsi Z hZ
    have hr : localWeak T.map := by
      apply Localization.weakEquivalences_le_localEquivalences localizingFamily
      change (InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ).categoryWithWeakEquivalences.weakEquivalences
        T.map
      rw [← ProjectiveInjectiveComparison.weakEquivalences_eq ReverseSimplexᵒᵖ]
      exact T.rowwiseWeak
    exact localWeak.comp_mem _ _ hψ hr
  letI : IsFibrant Z := hZ.1
  letI : IsFibrant T.target := T.localObject.1
  letI : IsFibrant (replacement.obj Z) := (replacement_local Z).1
  letI : IsFibrant (replacement.obj T.target) := (replacement_local T.target).1
  letI : IsFibrant (replacement.obj (Qproj.obj Z)) := (replacement_local (Qproj.obj Z)).1
  have htest : homotopyMappingWeakEquivalences T.target f :=
    (InjectiveKanDiagram.homotopyMappingWeakEquivalences_iff_strict ReverseSimplexᵒᵖ f).mpr
      (hf C)
  exact (homotopyMappingWeakEquivalences_target_iff (Z := Z)
    (replacementUnit.app Z) (replacementUnit_weak_of_local hZ) f).mpr
    ((homotopyMappingWeakEquivalences_target_iff
      (Z := replacement.obj (Qproj.obj Z)) (T := replacement.obj Z)
      (replacement.map (p.app Z)) (replacement_map_weak _ hp) f).mp
      ((homotopyMappingWeakEquivalences_target_iff
        (replacement.map g) (replacement_map_weak _ hg) f).mpr
        ((homotopyMappingWeakEquivalences_target_iff (Z := T.target)
          (replacementUnit.app T.target) (replacementUnit_weak_of_local T.localObject) f).mp
          htest)))

end

end DaggerModels.PartII.JTFrameNerveDetectionFromStrictification
