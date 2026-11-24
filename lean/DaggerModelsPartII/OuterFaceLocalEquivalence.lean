import DaggerModelsPartII.OuterFaceSpineGeometry
import DaggerModelsPartII.ReversalDiscreteFreeColimits
import DaggerModelsPartII.SegalLocalizationModels
import DaggerModelsPartII.LeftProperPushoutComparison

/-!
# Local equivalence of the outer-face inclusion

The two literal pushout squares of outer faces and spine parts are compared
in the injective Segal localization.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty

namespace DaggerModels.PartII.OuterFaceLocalEquivalence

open SegalLocalizers SpineOuterFacePushout OuterFaceSpineGeometry
open ReversalOuterFaceLocality ReversalDiscreteFreeColimits

noncomputable section

private def mapArrowIso {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B A' B' : C} {i : A ⟶ B} {j : A' ⟶ B'}
    (e : Arrow.mk i ≅ Arrow.mk j) :
    Arrow.mk (F.map i) ≅ Arrow.mk (F.map j) := by
  refine Arrow.isoMk (F.mapIso (Arrow.leftFunc.mapIso e))
    (F.mapIso (Arrow.rightFunc.mapIso e)) ?_
  simpa only [Functor.map_comp] using congrArg F.map e.hom.w

private theorem spine_eq_top_of_le_one (n : ℕ) (hn : n ≤ 1) :
    DaggerNativeStandardSpineInner.spine.{0} n = ⊤ := by
  apply top_unique
  intro q c hc
  induction q using Opposite.rec with | op q =>
    induction q using SimplexCategory.rec with | h d =>
      rw [DaggerNativeStandardSpineInner.mem_spine_iff]
      have hr := (SSet.stdSimplex.asOrderHom c (Fin.last d)).isLt
      omega

private theorem spine_ι_isIso_of_le_one (n : ℕ) (hn : n ≤ 1) :
    IsIso (DaggerNativeStandardSpineInner.spine.{0} n).ι := by
  rw [spine_eq_top_of_le_one n hn]
  change IsIso (SSet.Subcomplex.topIso (Δ[n] : SSet.{0})).hom
  infer_instance

private theorem localizerArrow_weak (i : LocalizerIndex) :
    injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
      (localizerArrow i).hom := by
  letI : ModelCategory ReverseDaggerSpace.{0} :=
    InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
  have h : InjectiveKanDiagram.diagramLocalizingFamily ReverseSimplexᵒᵖ
      LocalizerIndex localizerArrow (localizerArrow i).hom := by
    exact MorphismProperty.ofHoms.mk i
  have hw := Localization.family_le_localEquivalences
    (InjectiveKanDiagram.diagramLocalizingFamily ReverseSimplexᵒᵖ
      LocalizerIndex localizerArrow) _ h
  rw [show injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences =
    Localization.localEquivalences
      (InjectiveKanDiagram.diagramLocalizingFamily ReverseSimplexᵒᵖ
        LocalizerIndex localizerArrow) from
    (InjectiveKanDiagram.localized_exactClasses ReverseSimplexᵒᵖ
      LocalizerIndex localizerArrow localizerArrow_mono).2]
  exact hw

private theorem segalMap_weak (n : ℕ) (hn : 2 ≤ n) :
    injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
      (segalMap n) := by
  exact localizerArrow_weak (.inl ⟨n, hn⟩)

private theorem weak_map_spine_ι_of_le_one (n : ℕ) (hn : n ≤ 1) :
    injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
      (discreteFree.map (DaggerNativeStandardSpineInner.spine n).ι) := by
  letI : IsIso (DaggerNativeStandardSpineInner.spine.{0} n).ι :=
    spine_ι_isIso_of_le_one n hn
  letI : IsIso (discreteFree.map (DaggerNativeStandardSpineInner.spine n).ι) :=
    Functor.map_isIso _ _
  letI : ModelCategory ReverseDaggerSpace.{0} := injectiveSegalModel
  exact (weakEquivalences ReverseDaggerSpace.{0}).of_isIso _

private theorem weak_map_spine_ι (n : ℕ) :
    injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
      (discreteFree.map (DaggerNativeStandardSpineInner.spine n).ι) := by
  by_cases hn : 2 ≤ n
  · change injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
      (segalMap n)
    exact segalMap_weak n hn
  · exact weak_map_spine_ι_of_le_one n (by omega)

private theorem firstVertical_weak (t : ℕ) :
    injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
      (discreteFree.map (firstVertical t)) := by
  letI : ModelCategory ReverseDaggerSpace.{0} := injectiveSegalModel
  have h := weak_map_spine_ι (t + 1)
  exact ((weakEquivalences ReverseDaggerSpace.{0}).arrow_mk_iso_iff
    (mapArrowIso discreteFree (firstVerticalArrowIso t))).mp h

private theorem lastVertical_weak (t : ℕ) :
    injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
      (discreteFree.map (lastVertical t)) := by
  letI : ModelCategory ReverseDaggerSpace.{0} := injectiveSegalModel
  have h := weak_map_spine_ι (t + 1)
  exact ((weakEquivalences ReverseDaggerSpace.{0}).arrow_mk_iso_iff
    (mapArrowIso discreteFree (lastVerticalArrowIso t))).mp h

private theorem middleVertical_weak (t : ℕ) :
    injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
      (discreteFree.map (middleVertical t)) := by
  letI : ModelCategory ReverseDaggerSpace.{0} := injectiveSegalModel
  have h := weak_map_spine_ι t
  exact ((weakEquivalences ReverseDaggerSpace.{0}).arrow_mk_iso_iff
    (mapArrowIso discreteFree (middleVerticalArrowIso t))).mp h

private theorem cofibration_of_mono {A B : SSet.{0}} (i : A ⟶ B) [Mono i] :
    injectiveSegalModel.categoryWithCofibrations.cofibrations
      (discreteFree.map i) := by
  have h := (InjectiveKanDiagram.localized_exactClasses ReverseSimplexᵒᵖ
    LocalizerIndex localizerArrow localizerArrow_mono).1
  rw [h]
  letI : ModelCategory ReverseDaggerSpace.{0} :=
    InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
  change cofibrations ReverseDaggerSpace.{0} (discreteFree.map i)
  rw [InjectiveKanDiagram.model_cofibrations]
  exact map_mono i

private theorem firstSpan_comm (t : ℕ) :
    SSet.Subcomplex.homOfLE
        (inf_le_left : middleSpinePart.{0} t ≤ firstSpinePart t) ≫
      firstVertical t =
    middleVertical t ≫ SSet.Subcomplex.homOfLE
      (inf_le_left : middleFace.{0} t ≤ firstOuterFace t) := rfl

private theorem lastSpan_comm (t : ℕ) :
    SSet.Subcomplex.homOfLE
        (inf_le_right : middleSpinePart.{0} t ≤ lastSpinePart t) ≫
      lastVertical t =
    middleVertical t ≫ SSet.Subcomplex.homOfLE
      (inf_le_right : middleFace.{0} t ≤ lastOuterFace t) := rfl

private theorem firstApex_comm (t : ℕ) :
    SSet.Subcomplex.homOfLE
        (inf_le_left : firstSpinePart.{0} t ≤
          DaggerNativeStandardSpineInner.spine (t + 2)) ≫
      spineToOuterFaces t =
    firstVertical t ≫ SSet.Subcomplex.homOfLE
      (le_sup_left : firstOuterFace.{0} t ≤ ordinaryOuterFaces t) := rfl

private theorem lastApex_comm (t : ℕ) :
    SSet.Subcomplex.homOfLE
        (inf_le_left : lastSpinePart.{0} t ≤
          DaggerNativeStandardSpineInner.spine (t + 2)) ≫
      spineToOuterFaces t =
    lastVertical t ≫ SSet.Subcomplex.homOfLE
      (le_sup_right : lastOuterFace.{0} t ≤ ordinaryOuterFaces t) := rfl

/-- The ordinary spine-to-outer-face factor is locally weak after the actual
discrete free dagger completion. -/
theorem daggerSpineToOuterFaces_weak (t : ℕ) :
    injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
      (daggerSpineToOuterFaces t) := by
  letI : ModelCategory ReverseDaggerSpace.{0} := injectiveSegalModel
  have sq := map_isPushout (spinePartsPushout.{0} t)
  have sq' := map_isPushout (outerFacePushout.{0} t)
  have hi : cofibrations ReverseDaggerSpace.{0}
      (discreteFree.map (SSet.Subcomplex.homOfLE
        (inf_le_left : middleSpinePart.{0} t ≤ firstSpinePart t))) := by
    letI : Mono (SSet.Subcomplex.homOfLE
        (inf_le_left : middleSpinePart.{0} t ≤ firstSpinePart t)) := inferInstance
    exact cofibration_of_mono _
  have hi' : cofibrations ReverseDaggerSpace.{0}
      (discreteFree.map (SSet.Subcomplex.homOfLE
        (inf_le_left : middleFace.{0} t ≤ firstOuterFace t))) := by
    letI : Mono (SSet.Subcomplex.homOfLE
        (inf_le_left : middleFace.{0} t ≤ firstOuterFace t)) := inferInstance
    exact cofibration_of_mono _
  exact weak_of_pushoutComparison
    (fun sq₀ hi₀ hw₀ ↦ injectiveSegalModel_leftProper sq₀ hi₀ hw₀)
    sq sq' hi hi'
    (discreteFree.map (middleVertical t))
    (discreteFree.map (firstVertical t))
    (discreteFree.map (lastVertical t))
    (daggerSpineToOuterFaces t)
    (by simpa only [← Functor.map_comp] using congrArg discreteFree.map (firstSpan_comm t))
    (by simpa only [← Functor.map_comp] using congrArg discreteFree.map (lastSpan_comm t))
    (by
      change discreteFree.map _ ≫ discreteFree.map (spineToOuterFaces t) = _
      simpa only [← Functor.map_comp] using congrArg discreteFree.map (firstApex_comm t))
    (by
      change discreteFree.map _ ≫ discreteFree.map (spineToOuterFaces t) = _
      simpa only [← Functor.map_comp] using congrArg discreteFree.map (lastApex_comm t))
    (middleVertical_weak t) (firstVertical_weak t) (lastVertical_weak t)

/-- The outer-face inclusion is weak in the actual injective Segal localization. -/
theorem daggerOuterFaceMap_weak (t : ℕ) :
    injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
      (daggerOuterFaceMap t) := by
  letI : ModelCategory ReverseDaggerSpace.{0} := injectiveSegalModel
  letI : CategoryWithWeakEquivalences ReverseDaggerSpace.{0} :=
    injectiveSegalModel.categoryWithWeakEquivalences
  letI : (weakEquivalences ReverseDaggerSpace.{0}).HasTwoOutOfThreeProperty :=
    injectiveSegalModel.cm2
  have hcomp : weakEquivalences ReverseDaggerSpace.{0}
      (daggerSpineToOuterFaces t ≫ daggerOuterFaceMap t) := by
    rw [daggerSpineToOuterFaces_comp]
    exact segalMap_weak (t + 2) (by omega)
  exact (weakEquivalences ReverseDaggerSpace.{0}).of_precomp
    (W' := weakEquivalences ReverseDaggerSpace.{0}) _ _
    (daggerSpineToOuterFaces_weak t) hcomp

/-- The outer-face inclusion is a trivial cofibration in the manuscript's
injective Segal localization. -/
theorem daggerOuterFaceMap_trivialCofibration (t : ℕ) :
    @trivialCofibrations ReverseDaggerSpace.{0} _
      injectiveSegalModel.categoryWithCofibrations
      injectiveSegalModel.categoryWithWeakEquivalences
      _ _ (daggerOuterFaceMap t) := by
  constructor
  · change injectiveSegalModel.categoryWithCofibrations.cofibrations
      (daggerOuterFaceMap t)
    have h := (InjectiveKanDiagram.localized_exactClasses ReverseSimplexᵒᵖ
      LocalizerIndex localizerArrow localizerArrow_mono).1
    rw [h]
    letI : ModelCategory ReverseDaggerSpace.{0} :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
    change cofibrations ReverseDaggerSpace.{0} (daggerOuterFaceMap t)
    rw [InjectiveKanDiagram.model_cofibrations]
    exact daggerOuterFaceMap_mono t
  · exact daggerOuterFaceMap_weak t

end

end DaggerModels.PartII.OuterFaceLocalEquivalence
