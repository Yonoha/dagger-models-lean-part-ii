import DaggerModelsPartII.FunctorialCofibrantArrowResolution
import DaggerModelsPartII.ProjectiveSegalLocality

/-! The projective Segal localizers chosen by a single functorial arrow replacement. -/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra MorphismProperty

namespace DaggerModels.PartII.SegalLocalizers

noncomputable section

local instance : ModelCategory ReverseDaggerSpace.{0} :=
  ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ

/-- Apply the same functorial arrow resolution to every literal localizing map. -/
def functorialProjectiveResolution (i : LocalizerIndex) :
    CofibrantArrowResolution (localizerMap.{0} i).2.2 :=
  FunctorialCofibrantArrowResolution.Projective.component ReverseSimplex _

/-- The functorially chosen family of projectively cofibrant resolutions. -/
def functorialProjectiveSRev : MorphismProperty ReverseDaggerSpace.{0} :=
  ofHoms (fun i ↦ (functorialProjectiveResolution i).hom)

instance : IsSmall.{0} functorialProjectiveSRev := isSmall_ofHoms _

/-- This choice imposes precisely the same derived tests as the literal family. -/
theorem functorialProjectiveSRev_iff (Z : ReverseDaggerSpace.{0}) [IsFibrant Z] :
    functorialProjectiveSRev ≤ homotopyMappingWeakEquivalences Z ↔
      segalLocalizingFamily ≤ homotopyMappingWeakEquivalences Z :=
  resolvedFamily_le_iff _ functorialProjectiveResolution Z

theorem functorialProjectiveSRev_localObjects (Z : ReverseDaggerSpace.{0}) :
    Localization.localObject functorialProjectiveSRev Z ↔
      Localization.localObject segalLocalizingFamily Z := by
  constructor
  · rintro ⟨hZ, h⟩
    letI := hZ
    exact ⟨hZ, (functorialProjectiveSRev_iff Z).mp h⟩
  · rintro ⟨hZ, h⟩
    letI := hZ
    exact ⟨hZ, (functorialProjectiveSRev_iff Z).mpr h⟩

/-- The functorial choice leaves the exact local-equivalence class unchanged. -/
theorem functorialProjectiveSRev_localEquivalences :
    Localization.localEquivalences functorialProjectiveSRev =
      Localization.localEquivalences segalLocalizingFamily :=
  Localization.localEquivalences_eq_of_localObjects _ _ functorialProjectiveSRev_localObjects

variable {D : Type} [SmallCategory D] (F : ReverseSimplex ⥤ D)

local instance : ModelCategory (Dᵒᵖ ⥤ SSet.{0}) :=
  ProjectiveKanDiagram.modelCategory Dᵒᵖ

/-- The actual left Kan images of the functorially resolved Segal maps. -/
def functorialImageSRev : MorphismProperty (Dᵒᵖ ⥤ SSet.{0}) :=
  ofHoms (fun i ↦ (extendIndexLeft.{0, 0} F).map (functorialProjectiveResolution i).hom)

/-- Derived locality at these left Kan images is the original locality after restriction. -/
theorem functorialImageSRev_iff (Z : Dᵒᵖ ⥤ SSet.{0}) [IsFibrant Z] :
    functorialImageSRev F ≤ homotopyMappingWeakEquivalences Z ↔
      segalLocalizingFamily ≤ homotopyMappingWeakEquivalences ((restrictIndex.{0, 0} F).obj Z) := by
  letI := projectiveIndexAdjunction_isQuillen F
  letI := projectiveRestriction_isFibrant F Z
  letI : ∀ i, IsCofibrant (functorialProjectiveResolution i).source :=
    fun i ↦ (functorialProjectiveResolution i).source_cofibrant
  letI : ∀ i, IsCofibrant (functorialProjectiveResolution i).target :=
    fun i ↦ (functorialProjectiveResolution i).target_cofibrant
  exact (leftQuillen_imageLocality_iff
    (fun i ↦ (functorialProjectiveResolution i).hom) (extendIndexLeftAdjunction F) Z).trans
      (functorialProjectiveSRev_iff _)

end

end DaggerModels.PartII.SegalLocalizers
