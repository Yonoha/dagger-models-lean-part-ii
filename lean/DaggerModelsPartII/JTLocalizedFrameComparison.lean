import DaggerModelsPartII.JTProjectiveFrameRealization
import DaggerModelsPartII.JTFunctorialBergnerReplacement
import DaggerModelsPartII.JTFrameDerivedUnitFromStrictification
import DaggerModelsPartII.LocalizedWeakFunctors
import ProofActualDaggerQuillenEquivalence

/-! The original frame realization is faithful after localization once the
chosen strictification is locally weak. The constant-vertex composite
compares to Part I's literal rigidification. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTLocalizedFrameComparison

open SegalLocalizers LocalizedWeakFunctors JTFrameAdjunction
open JTStrictificationMaps JTStrictificationCoefficients JTProjectiveFrameRealization
open ConstantVertexAdjunction
open OrdinaryRigidification.DaggerRigidification OrdinaryRigidification.DaggerNerve

noncomputable section

private abbrev S := ReverseDaggerSpace.{0}
private abbrev D := DaggerSSet.{0}
private abbrev B := DaggerSimplicialCat.{0, 0}

private local instance : ModelCategory S := injectiveSegalModel
private local instance : ModelCategory D := DaggerActualRigidificationQuillen.modelD.{0}
private local instance : ModelCategory B := DaggerActualRigidificationQuillen.modelG.{0}
private local instance : HasLimits D := daggerSSetHasLimits
private local instance : HasColimits D := daggerSSetHasColimits
private local instance : HasLimits B := daggerSimplicialCatHasLimits
private local instance : HasColimits B := daggerSimplicialCatHasColimits

private abbrev WS := weakEquivalences S
private abbrev WD := weakEquivalences D
private abbrev WB := weakEquivalences B

/-- The remaining strictification input, in the original injective-local model. -/
abbrev ChosenPsiWeak : Prop :=
  ∀ Z, (letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
    Localization.localObject localizingFamily Z) → WS (chosenPsi Z)

private theorem projectiveWeak_eq :
    projectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences = WS := by
  change projectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences =
    injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
  rw [(ProjectiveKanDiagram.localized_exactClasses ReverseSimplexᵒᵖ LocalizerIndex
      localizerArrow localizerArrow_mono).2,
    (InjectiveKanDiagram.localized_exactClasses ReverseSimplexᵒᵖ LocalizerIndex
      localizerArrow localizerArrow_mono).2]
  exact ProjectiveInjectiveComparison.localEquivalences_eq _ _

private theorem p_weak (X : S) : WS (p.app X) := by
  change injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences (p.app X)
  rw [(InjectiveKanDiagram.localized_exactClasses ReverseSimplexᵒᵖ LocalizerIndex
    localizerArrow localizerArrow_mono).2]
  letI : ModelCategory S := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
  apply Localization.weakEquivalences_le_localEquivalences localizingFamily
  change (InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ).categoryWithWeakEquivalences.weakEquivalences (p.app X)
  rw [← ProjectiveInjectiveComparison.weakEquivalences_eq ReverseSimplexᵒᵖ]
  exact (p_trivialFibration X).2

private theorem Qproj_weak : WS ≤ WS.inverseImage Qproj := by
  intro X Y f hf
  apply WS.of_postcomp _ _ (p_weak Y)
  rw [p.naturality f]
  exact WS.comp_mem _ _ (p_weak X) hf

private theorem frame_weak : WS ≤ WB.inverseImage projectiveFrameRealization := by
  intro X Y f hf
  apply projectiveFrameRealization_map_weak f
  change projectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences f
  rwa [projectiveWeak_eq]

private abbrev bergnerReplacement := JTFunctorialBergnerReplacement.replacement
private abbrev bergnerUnit := JTFunctorialBergnerReplacement.unit
private abbrev frameRight := bergnerReplacement ⋙ frameNerve

private theorem frameRight_weak : WB ≤ WS.inverseImage frameRight := by
  intro X Y f hf
  rw [← projectiveWeak_eq]
  letI : ModelCategory S := projectiveSegalModel
  letI : JTFrameAdjunction.adjunction.IsQuillenAdjunction :=
    JTSegalFrameLocality.localized_isQuillenAdjunction
  exact rightAfterReplacement_map_weak JTFrameAdjunction.adjunction
    bergnerReplacement bergnerUnit JTFunctorialBergnerReplacement.isFibrant
      JTFunctorialBergnerReplacement.unit_weak f hf

private abbrev segalReplacement :=
  InjectiveKanDiagram.localReplacement ReverseSimplexᵒᵖ LocalizerIndex localizerArrow
private abbrev segalUnit :=
  InjectiveKanDiagram.localReplacementUnit ReverseSimplexᵒᵖ LocalizerIndex localizerArrow

private theorem segalUnit_weak (X : S) : WS (segalUnit.app X) := by
  change injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences (segalUnit.app X)
  rw [(InjectiveKanDiagram.localized_exactClasses ReverseSimplexᵒᵖ LocalizerIndex
    localizerArrow localizerArrow_mono).2]
  exact InjectiveKanDiagram.localReplacementUnit_localEquivalence _ _ _ localizerArrow_mono X

private def frameUnit : Qproj ⟶ projectiveFrameRealization ⋙ frameRight :=
  Functor.whiskerLeft Qproj JTFrameAdjunction.adjunction.unit ≫
    Functor.whiskerRight (Functor.whiskerLeft projectiveFrameRealization bergnerUnit) frameNerve

private theorem frameUnit_weak (hpsi : ChosenPsiWeak) (X : S) :
    WS (frameUnit.app X) := by
  have hy : WS (frameUnit.app (segalReplacement.obj X)) := by
    let Y := segalReplacement.obj X
    letI := JTFunctorialBergnerReplacement.isFibrant (projectiveFrameRealization.obj Y)
    have hY := InjectiveKanDiagram.localReplacement_isLocal
      ReverseSimplexᵒᵖ LocalizerIndex localizerArrow localizerArrow_mono X
    have h := JTFrameDerivedUnitFromStrictification.frameAdjoint_weak_of_chosenPsi_weak Y
      (hpsi Y hY) _ (JTFunctorialBergnerReplacement.unit_weak
        (projectiveFrameRealization.obj Y))
    simpa only [Adjunction.homEquiv_unit, frameUnit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app] using h
  have hcomp : WS ((projectiveFrameRealization ⋙ frameRight).map (segalUnit.app X)) :=
    frameRight_weak _ (frame_weak _ (segalUnit_weak X))
  apply WS.of_postcomp _ _ hcomp
  have hnat := frameUnit.naturality (segalUnit.app X)
  change Qproj.map (segalUnit.app X) ≫ frameUnit.app (segalReplacement.obj X) =
    frameUnit.app X ≫ (projectiveFrameRealization ⋙ frameRight).map (segalUnit.app X) at hnat
  rw [← hnat]
  exact WS.comp_mem _ _ (Qproj_weak _ (segalUnit_weak X)) hy

private theorem weakId {A : Type*} [Category* A] (W : MorphismProperty A) :
    W ≤ W.inverseImage (𝟭 A) := fun _ _ _ hf ↦ hf

private theorem frame_faithful (hpsi : ChosenPsiWeak) : (lift frame_weak).Faithful := by
  let hcomp : WS ≤ WS.inverseImage (projectiveFrameRealization ⋙ frameRight) :=
    fun _ _ f hf ↦ frameRight_weak _ (frame_weak f hf)
  exact Functor.Faithful.of_comp_iso
    (compIso frame_weak frameRight_weak hcomp ≪≫
      (mapIso Qproj_weak hcomp frameUnit (frameUnit_weak hpsi)).symm ≪≫
      mapIso Qproj_weak (weakId WS) p p_weak ≪≫ idIso (weakId WS))

private abbrev rigidRight := bergnerReplacement ⋙ daggerCoherentNerve

private theorem rigid_weak : WD ≤ WB.inverseImage daggerRigidification := by
  intro X Y f hf
  exact (weakEquivalence_iff _).mp ((DaggerActualQuillenEquivalenceReduction.weakEquivalence_map_iff
    f).mpr ((weakEquivalence_iff _).mpr hf))

private theorem rigidRight_weak : WB ≤ WD.inverseImage rigidRight := by
  letI : DaggerActualRigidificationQuillen.adjunction.{0}.IsQuillenAdjunction :=
    DaggerActualRigidificationQuillen.isQuillen
  exact rightAfterReplacement_map_weak DaggerActualRigidificationQuillen.adjunction
    bergnerReplacement bergnerUnit JTFunctorialBergnerReplacement.isFibrant
      JTFunctorialBergnerReplacement.unit_weak

private theorem bergnerReplacement_weak : WB ≤ WB.inverseImage bergnerReplacement := by
  intro X Y f hf
  apply WB.of_precomp _ _ (JTFunctorialBergnerReplacement.unit_weak X)
  rw [← bergnerUnit.naturality f]
  exact WB.comp_mem _ _ hf (JTFunctorialBergnerReplacement.unit_weak Y)

private abbrev rigidAdj := DaggerActualRigidificationQuillen.adjunction.{0}

private def rigidUnit : 𝟭 D ⟶ daggerRigidification ⋙ rigidRight :=
  rigidAdj.unit ≫ Functor.whiskerRight (Functor.whiskerLeft daggerRigidification bergnerUnit)
    daggerCoherentNerve

private def rigidCounit : rigidRight ⋙ daggerRigidification ⟶ bergnerReplacement :=
  Functor.whiskerLeft bergnerReplacement rigidAdj.counit

private theorem rigidCounit_weak (X : B) : WB (rigidCounit.app X) :=
  (weakEquivalence_iff _).mp
    (DaggerActualFibrantCounitReduction.fibrant_counit_weak_of_ordinary_local
      DaggerActualDaggerQuillenEquivalenceProof.counit_verified (bergnerReplacement.obj X)
        (JTFunctorialBergnerReplacement.isFibrant X))

private theorem rigidUnit_weak (X : D) : WD (rigidUnit.app X) := by
  apply (weakEquivalence_iff _).mp
  apply (DaggerActualQuillenEquivalenceReduction.weakEquivalence_map_iff _).mp
  apply (weakEquivalence_iff _).mpr
  apply WB.of_postcomp _ _ (rigidCounit_weak (daggerRigidification.obj X))
  let C := bergnerReplacement.obj (daggerRigidification.obj X)
  let b : daggerRigidification.obj X ⟶ C := bergnerUnit.app (daggerRigidification.obj X)
  have h : daggerRigidification.map ((rigidAdj.homEquiv X C) b) ≫
      rigidAdj.counit.app C = b :=
    (rigidAdj.homEquiv_counit X C ((rigidAdj.homEquiv X C) b)).symm.trans
      (Equiv.symm_apply_apply _ _)
  rw [rigidAdj.homEquiv_unit] at h
  change WB (daggerRigidification.map (rigidAdj.unit.app X ≫ daggerCoherentNerve.map b) ≫
    rigidAdj.counit.app C)
  rw [h]
  exact JTFunctorialBergnerReplacement.unit_weak _

private def rigidEquivalence : WD.Localization ≌ WB.Localization := by
  let hL : WD ≤ WD.inverseImage (daggerRigidification ⋙ rigidRight) :=
    fun _ _ f hf ↦ rigidRight_weak _ (rigid_weak f hf)
  let hR : WB ≤ WB.inverseImage (rigidRight ⋙ daggerRigidification) :=
    fun _ _ f hf ↦ rigid_weak _ (rigidRight_weak f hf)
  exact CategoryTheory.Equivalence.mk (lift rigid_weak) (lift rigidRight_weak)
    ((idIso (weakId WD)).symm ≪≫ mapIso (weakId WD) hL rigidUnit rigidUnit_weak ≪≫
      (compIso rigid_weak rigidRight_weak hL).symm)
    (compIso rigidRight_weak rigid_weak hR ≪≫
      mapIso hR bergnerReplacement_weak rigidCounit rigidCounit_weak ≪≫
      (mapIso (weakId WB) bergnerReplacement_weak bergnerUnit
        JTFunctorialBergnerReplacement.unit_weak).symm ≪≫ idIso (weakId WB))

/-- Detection by the chosen frame tests yields preservation on all original weak maps. -/
theorem delta_weak (hpsi : ChosenPsiWeak) : WD ≤ WS.inverseImage delta := by
  intro X Y f hf
  apply JTFrameNerveDetectionFromStrictification.detect_weak_of_chosenPsi hpsi
  intro C hC
  apply JTDeltaFrameNerveTests.deltaMap_weak_strictMappingTest f _ C
  rwa [← DaggerActualRigidificationQuillen.source_weak]

/-- The original constant-vertex functor is fully faithful after localization
under the literal strictification input. -/
def localizedDelta_fullyFaithful (hpsi : ChosenPsiWeak) : (lift (delta_weak hpsi)).FullyFaithful := by
  let hcomp : WD ≤ WB.inverseImage (delta ⋙ projectiveFrameRealization) :=
    fun _ _ f hf ↦ frame_weak _ (delta_weak hpsi f hf)
  let e := compIso (delta_weak hpsi) frame_weak hcomp ≪≫
    mapIso hcomp rigid_weak compareRigidification compareRigidification_weak
  letI : (lift rigid_weak).IsEquivalence := rigidEquivalence.isEquivalence_functor
  letI : (lift frame_weak).Faithful := frame_faithful hpsi
  exact Functor.FullyFaithful.ofCompFaithful ((Functor.FullyFaithful.ofFullyFaithful _).ofIso e.symm)

end

end DaggerModels.PartII.JTLocalizedFrameComparison
