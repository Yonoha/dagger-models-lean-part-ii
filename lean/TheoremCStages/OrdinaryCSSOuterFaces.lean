import DaggerModelsPartII.OuterFaceSpineGeometry
import DaggerModelsPartII.ReversalDiscreteFreeColimits
import OrdinaryCSSLocalization
import DaggerModelsPartII.LeftProperPushoutComparison

/-!
# Ordinary CSS weakness of the union of the two outer faces

Reuse the exact existing spine/outerface pushout geometry and left-proper
pushout comparison with horizontal ordinary discretization. The target is
the actual ordinary CSS localization, not the reversal-diagram model.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty

namespace DaggerModels.PartII.OrdinaryCSSOuterFaces

open OrdinaryCSSLocalization SpineOuterFacePushout OuterFaceSpineGeometry
open ReversalOuterFaceLocality

noncomputable section

private instance : PreservesColimitsOfShape WalkingSpan discrete := by
  letI : PreservesColimitsOfShape WalkingSpan (SimplicialObject.const (Type 0)) :=
    (CategoryTheory.Limits.preservesColimits_const
      (D := SimplexCategoryᵒᵖ)).preservesColimitsOfShape
  change PreservesColimitsOfShape WalkingSpan
    ((Functor.whiskeringRight SimplexCategoryᵒᵖ (Type 0) SSet.{0}).obj
      (SimplicialObject.const (Type 0)))
  infer_instance

private theorem map_isPushout {A B D P : SSet.{0}} {i : A ⟶ B} {k : A ⟶ D}
    {l : B ⟶ P} {r : D ⟶ P} (sq : IsPushout i k l r) :
    IsPushout (discrete.map i) (discrete.map k)
      (discrete.map l) (discrete.map r) := sq.map discrete


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
    model.categoryWithWeakEquivalences.weakEquivalences
      (localizerArrow i).hom := by
  letI : ModelCategory Space :=
    InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ
  have h : InjectiveKanDiagram.diagramLocalizingFamily SimplexCategoryᵒᵖ
      LocalizerIndex localizerArrow (localizerArrow i).hom := by
    exact MorphismProperty.ofHoms.mk i
  have hw := Localization.family_le_localEquivalences
    (InjectiveKanDiagram.diagramLocalizingFamily SimplexCategoryᵒᵖ
      LocalizerIndex localizerArrow) _ h
  rw [show model.categoryWithWeakEquivalences.weakEquivalences =
    Localization.localEquivalences
      (InjectiveKanDiagram.diagramLocalizingFamily SimplexCategoryᵒᵖ
        LocalizerIndex localizerArrow) from
    (InjectiveKanDiagram.localized_exactClasses SimplexCategoryᵒᵖ
      LocalizerIndex localizerArrow localizerArrow_mono).2]
  exact hw

private theorem segalMap_weak (n : ℕ) (hn : 2 ≤ n) :
    model.categoryWithWeakEquivalences.weakEquivalences
      (spineMap n) := by
  exact localizerArrow_weak (.inl ⟨n, hn⟩)

private theorem weak_map_spine_ι_of_le_one (n : ℕ) (hn : n ≤ 1) :
    model.categoryWithWeakEquivalences.weakEquivalences
      (discrete.map (DaggerNativeStandardSpineInner.spine n).ι) := by
  letI : IsIso (DaggerNativeStandardSpineInner.spine.{0} n).ι :=
    spine_ι_isIso_of_le_one n hn
  letI : IsIso (discrete.map (DaggerNativeStandardSpineInner.spine n).ι) :=
    Functor.map_isIso _ _
  letI : ModelCategory Space := model
  exact (weakEquivalences Space).of_isIso _

private theorem weak_map_spine_ι (n : ℕ) :
    model.categoryWithWeakEquivalences.weakEquivalences
      (discrete.map (DaggerNativeStandardSpineInner.spine n).ι) := by
  by_cases hn : 2 ≤ n
  · change model.categoryWithWeakEquivalences.weakEquivalences
      (spineMap n)
    exact segalMap_weak n hn
  · exact weak_map_spine_ι_of_le_one n (by omega)

private theorem firstVertical_weak (t : ℕ) :
    model.categoryWithWeakEquivalences.weakEquivalences
      (discrete.map (firstVertical t)) := by
  letI : ModelCategory Space := model
  have h := weak_map_spine_ι (t + 1)
  exact ((weakEquivalences Space).arrow_mk_iso_iff
    (mapArrowIso discrete (firstVerticalArrowIso t))).mp h

private theorem lastVertical_weak (t : ℕ) :
    model.categoryWithWeakEquivalences.weakEquivalences
      (discrete.map (lastVertical t)) := by
  letI : ModelCategory Space := model
  have h := weak_map_spine_ι (t + 1)
  exact ((weakEquivalences Space).arrow_mk_iso_iff
    (mapArrowIso discrete (lastVerticalArrowIso t))).mp h

private theorem middleVertical_weak (t : ℕ) :
    model.categoryWithWeakEquivalences.weakEquivalences
      (discrete.map (middleVertical t)) := by
  letI : ModelCategory Space := model
  have h := weak_map_spine_ι t
  exact ((weakEquivalences Space).arrow_mk_iso_iff
    (mapArrowIso discrete (middleVerticalArrowIso t))).mp h

private theorem cofibration_of_mono {A B : SSet.{0}} (i : A ⟶ B) [Mono i] :
    model.categoryWithCofibrations.cofibrations
      (discrete.map i) := by
  have h := (InjectiveKanDiagram.localized_exactClasses SimplexCategoryᵒᵖ
    LocalizerIndex localizerArrow localizerArrow_mono).1
  rw [h]
  letI : ModelCategory Space :=
    InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ
  change cofibrations Space (discrete.map i)
  rw [InjectiveKanDiagram.model_cofibrations]
  exact discrete_map_mono i

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
ordinary horizontal discretization. -/
theorem spineToOuterFaces_weak (t : ℕ) :
    model.categoryWithWeakEquivalences.weakEquivalences
      (discrete.map (spineToOuterFaces t)) := by
  letI : ModelCategory Space := model
  have sq := map_isPushout (spinePartsPushout.{0} t)
  have sq' := map_isPushout (outerFacePushout.{0} t)
  have hi : cofibrations Space
      (discrete.map (SSet.Subcomplex.homOfLE
        (inf_le_left : middleSpinePart.{0} t ≤ firstSpinePart t))) := by
    letI : Mono (SSet.Subcomplex.homOfLE
        (inf_le_left : middleSpinePart.{0} t ≤ firstSpinePart t)) := inferInstance
    exact cofibration_of_mono _
  have hi' : cofibrations Space
      (discrete.map (SSet.Subcomplex.homOfLE
        (inf_le_left : middleFace.{0} t ≤ firstOuterFace t))) := by
    letI : Mono (SSet.Subcomplex.homOfLE
        (inf_le_left : middleFace.{0} t ≤ firstOuterFace t)) := inferInstance
    exact cofibration_of_mono _
  exact weak_of_pushoutComparison
    (fun sq₀ hi₀ hw₀ ↦ InjectiveKanDiagram.localized_leftProper SimplexCategoryᵒᵖ
      LocalizerIndex localizerArrow localizerArrow_mono sq₀ hi₀ hw₀)
    sq sq' hi hi'
    (discrete.map (middleVertical t))
    (discrete.map (firstVertical t))
    (discrete.map (lastVertical t))
    (discrete.map (spineToOuterFaces t))
    (by simpa only [← Functor.map_comp] using congrArg discrete.map (firstSpan_comm t))
    (by simpa only [← Functor.map_comp] using congrArg discrete.map (lastSpan_comm t))
    (by
      change discrete.map _ ≫ discrete.map (spineToOuterFaces t) = _
      simpa only [← Functor.map_comp] using congrArg discrete.map (firstApex_comm t))
    (by
      change discrete.map _ ≫ discrete.map (spineToOuterFaces t) = _
      simpa only [← Functor.map_comp] using congrArg discrete.map (lastApex_comm t))
    (middleVertical_weak t) (firstVertical_weak t) (lastVertical_weak t)

/-- The outer-face inclusion is weak in the actual ordinary CSS localization. -/
theorem outerFaceMap_weak (t : ℕ) :
    model.categoryWithWeakEquivalences.weakEquivalences
      (discrete.map (ordinaryOuterFaces t).ι) := by
  letI : ModelCategory Space := model
  letI : CategoryWithWeakEquivalences Space :=
    model.categoryWithWeakEquivalences
  letI : (weakEquivalences Space).HasTwoOutOfThreeProperty :=
    model.cm2
  have hcomp : weakEquivalences Space
      (discrete.map (spineToOuterFaces t) ≫ discrete.map (ordinaryOuterFaces t).ι) := by
    rw [← discrete.map_comp, spineToOuterFaces_ι]
    exact segalMap_weak (t + 2) (by omega)
  exact (weakEquivalences Space).of_precomp
    (W' := weakEquivalences Space) _ _
    (spineToOuterFaces_weak t) hcomp

/-- The outer-face inclusion is a trivial cofibration in the ordinary CSS
localization. -/
theorem outerFaceMap_trivialCofibration (t : ℕ) :
    @trivialCofibrations Space _
      model.categoryWithCofibrations
      model.categoryWithWeakEquivalences
      _ _ (discrete.map (ordinaryOuterFaces t).ι) := by
  constructor
  · change model.categoryWithCofibrations.cofibrations
      (discrete.map (ordinaryOuterFaces t).ι)
    have h := (InjectiveKanDiagram.localized_exactClasses SimplexCategoryᵒᵖ
      LocalizerIndex localizerArrow localizerArrow_mono).1
    rw [h]
    letI : ModelCategory Space :=
      InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ
    change cofibrations Space (discrete.map (ordinaryOuterFaces t).ι)
    rw [InjectiveKanDiagram.model_cofibrations]
    exact discrete_map_mono (ordinaryOuterFaces t).ι
  · exact outerFaceMap_weak t

#print axioms spineToOuterFaces_weak
#print axioms outerFaceMap_weak
#print axioms outerFaceMap_trivialCofibration

end

end DaggerModels.PartII.OrdinaryCSSOuterFaces
