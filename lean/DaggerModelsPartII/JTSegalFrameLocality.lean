import DaggerModelsPartII.JTWalkingUnitaryWeak
import DaggerModelsPartII.JTSpineWeak
import DaggerModelsPartII.JTCofibrantAugmentationWeak
import DaggerModelsPartII.SegalLocalizationModels
import DaggerModelsPartII.JTFrameQuillen
import DaggerModelsPartII.LeftLocalizedQuillenDescent

/-!
# Derived Segal locality of the actual frame nerve and localized adjunction

The fixed functorial projective resolutions of the original Segal and
completeness generators have weak actual frame images. The original frame
nerve is consequently derived local on every fibrant dagger simplicial
category, and the original frame adjunction descends to the specified
projective Segal localization.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty DaggerModels

namespace DaggerModels.PartII.JTSegalFrameLocality

open SegalLocalizers JTFrameAdjunction

noncomputable section

private local instance : HasLimits DaggerSimplicialCat.{0, 0} :=
  daggerSimplicialCatHasLimits
private local instance : HasColimits DaggerSimplicialCat.{0, 0} :=
  daggerSimplicialCatHasColimits
private local instance : ModelCategory ReverseDaggerSpace.{0} :=
  ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
private local instance : ModelCategory DaggerSimplicialCat.{0, 0} :=
  DaggerActualRigidificationQuillen.modelG.{0}

/-- The exact original frame nerve of a fibrant target is projectively fibrant. -/
theorem frameNerve_obj_isFibrant (D : DaggerSimplicialCat.{0, 0}) [IsFibrant D] :
    IsFibrant (frameNerve.obj D) := by
  letI : adjunction.IsQuillenAdjunction := JTFrameQuillen.isQuillenAdjunction
  letI : frameNerve.PreservesFibrations :=
    Adjunction.IsQuillenAdjunction.preservesFibrations adjunction
  letI : PreservesLimits frameNerve := adjunction.rightAdjoint_preservesLimits
  have hT : IsTerminal (frameNerve.obj (⊤_ DaggerSimplicialCat.{0, 0})) :=
    terminalIsTerminal.isTerminalObj frameNerve _
  exact (isFibrant_iff_of_isTerminal
    (frameNerve.map (terminal.from D)) hT).2 inferInstance

/-- Every member of the fixed functorial projective localizer resolution
has weak image under the actual frame realization. -/
theorem frameRealization_localizerResolution_weak (i : LocalizerIndex) :
    weakEquivalences DaggerSimplicialCat.{0, 0}
      (frameRealization.map (functorialProjectiveResolution i).hom) := by
  cases i with
  | inl n =>
    exact JTCofibrantAugmentationWeak.frameRealization_resolution_weak
      (freeDagger.map (DaggerNativeStandardSpineInner.spine n.val).ι)
      (JTSpineWeak.spineFree_weak n.val) (functorialProjectiveResolution (.inl n))
  | inr e =>
    exact JTWalkingUnitaryWeak.frameRealization_completeness_resolution_weak
      (functorialProjectiveResolution (.inr e))

/-- The frame nerve of every fibrant original dagger simplicial category
is derived local for the exact functorially resolved Segal family. -/
theorem frameNerve_localObject (D : DaggerSimplicialCat.{0, 0}) [IsFibrant D] :
    Localization.localObject functorialProjectiveSRev (frameNerve.obj D) := by
  letI : IsFibrant (frameNerve.obj D) := frameNerve_obj_isFibrant D
  letI : adjunction.IsQuillenAdjunction := JTFrameQuillen.isQuillenAdjunction
  refine ⟨inferInstance, ?_⟩
  intro A B f hf
  obtain ⟨i⟩ := hf
  let R := functorialProjectiveResolution i
  letI hsource : IsCofibrant R.source := R.source_cofibrant
  letI htarget : IsCofibrant R.target := R.target_cofibrant
  apply (homotopyMappingWeakEquivalences_leftQuillen_iff adjunction R.hom D).1
  exact weakEquivalences_le_homotopyMappingWeakEquivalences D _
    (frameRealization_localizerResolution_weak i)


/-- The frame nerve is derived local for the literal manuscript family,
not only its selected functorial projective resolutions. -/
theorem frameNerve_literal_localObject (D : DaggerSimplicialCat.{0, 0})
    [IsFibrant D] :
    Localization.localObject segalLocalizingFamily (frameNerve.obj D) :=
  (functorialProjectiveSRev_localObjects _).1 (frameNerve_localObject D)

/-- The original frame adjunction descends to the exact projective Segal
localization, with the original dagger Bergner model unchanged. -/
theorem localized_isQuillenAdjunction :
    @Adjunction.IsQuillenAdjunction ReverseDaggerSpace.{0}
      DaggerSimplicialCat.{0, 0} _ _ projectiveSegalModel
      DaggerActualRigidificationQuillen.modelG.{0}
      frameRealization frameNerve adjunction := by
  apply Localization.leftLocalizedQuillen_of_rightFibrantLocal
    (ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ)
    DaggerActualRigidificationQuillen.modelG.{0}
    functorialProjectiveSRev projectiveSegalModel
    (ProjectiveKanDiagram.localized_exactClasses ReverseSimplexᵒᵖ
      LocalizerIndex localizerArrow localizerArrow_mono).1
    projectiveSegalModel_weakEquivalences frameRealization frameNerve adjunction
    JTFrameQuillen.isQuillenAdjunction
  intro D hD
  letI : IsFibrant D := hD
  exact frameNerve_localObject D

end

end DaggerModels.PartII.JTSegalFrameLocality
