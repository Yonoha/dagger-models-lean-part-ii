import DaggerModelsPartII.CofibrantLocalizingFamily
import DaggerModelsPartII.IndexProjectiveComparison
import DaggerModelsPartII.ProjectiveKanDiagram
import DaggerModelsPartII.SegalLocalizers
import DaggerModelsPartII.LocalEquivalenceClasses

/-! The projective locality test for the reversal Segal family and its left Kan image. -/

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.SegalLocalizers

noncomputable section

local instance reversalProjectiveModel : ModelCategory ReverseDaggerSpace.{0} :=
  ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ

/-- The literal original family as a morphism property. -/
def segalLocalizingFamily : MorphismProperty ReverseDaggerSpace.{0} :=
  localizingFamily

/-- The projectively cofibrant resolutions of the literal original family. -/
def projectiveSegalLocalizingFamily : MorphismProperty ReverseDaggerSpace.{0} :=
  cofibrantLocalizingFamily (fun i : LocalizerIndex ↦ (localizerMap i).2.2)

/-- For projectively fibrant objects, the original and resolved families
give the same derived locality test. -/
theorem projectiveSegalLocalizingFamily_iff (Z : ReverseDaggerSpace.{0}) [IsFibrant Z] :
    projectiveSegalLocalizingFamily ≤ homotopyMappingWeakEquivalences Z ↔
      segalLocalizingFamily ≤ homotopyMappingWeakEquivalences Z :=
  cofibrantLocalizingFamily_le_iff _ Z

variable {D : Type} [SmallCategory D] (F : ReverseSimplex ⥤ D)

local instance indexProjectiveModel : ModelCategory (Dᵒᵖ ⥤ SSet.{0}) :=
  ProjectiveKanDiagram.modelCategory Dᵒᵖ

/-- Change of index is Quillen for the two actual projective structures. -/
theorem projectiveIndexAdjunction_isQuillen :
    (extendIndexLeftAdjunction.{0, 0} F).IsQuillenAdjunction :=
  extendIndexLeft_isQuillen.{0, 0} F rfl rfl rfl rfl

/-- The projective localizers in the target are the actual left Kan images
of the cofibrantly resolved reversal Segal family. -/
def indexProjectiveSegalLocalizingFamily : MorphismProperty (Dᵒᵖ ⥤ SSet.{0}) :=
  imageCofibrantLocalizingFamily (L := extendIndexLeft.{0, 0} F)
    (fun i : LocalizerIndex ↦ (localizerMap i).2.2)

/-- Restriction preserves fibrant objects in the projective structures. -/
theorem projectiveRestriction_isFibrant (W : Dᵒᵖ ⥤ SSet.{0}) [IsFibrant W] :
    IsFibrant ((restrictIndex.{0, 0} F).obj W) := by
  let adj := extendIndexLeftAdjunction.{0, 0} F
  letI : adj.IsQuillenAdjunction := projectiveIndexAdjunction_isQuillen F
  let R := restrictIndex.{0, 0} F
  letI : R.PreservesFibrations := Adjunction.IsQuillenAdjunction.preservesFibrations adj
  letI : PreservesLimitsOfSize.{0, 0} R := adj.rightAdjoint_preservesLimits
  exact (isFibrant_iff_of_isTerminal (R.map (terminal.from W))
    (terminalIsTerminal.isTerminalObj R)).mpr inferInstance

/-- On a projectively fibrant target, locality at the left Kan image is equivalent
to derived locality at the reversal Segal maps after restriction. -/
theorem indexProjectiveSegalLocalizingFamily_iff (W : Dᵒᵖ ⥤ SSet.{0}) [IsFibrant W] :
    indexProjectiveSegalLocalizingFamily F ≤ homotopyMappingWeakEquivalences W ↔
      segalLocalizingFamily ≤ homotopyMappingWeakEquivalences ((restrictIndex.{0, 0} F).obj W) := by
  let adj := extendIndexLeftAdjunction.{0, 0} F
  letI : adj.IsQuillenAdjunction := projectiveIndexAdjunction_isQuillen F
  letI := projectiveRestriction_isFibrant F W
  exact leftQuillen_imageCofibrantLocality_iff _ adj W

/-- The resolved family specifies exactly the original local weak class. -/
theorem projectiveSegalLocalEquivalences_eq :
    Localization.localEquivalences projectiveSegalLocalizingFamily =
      Localization.localEquivalences segalLocalizingFamily :=
  Localization.cofibrantFamily_localEquivalences _

/-- The projective locality comparison, including fibrancy of the restricted target. -/
theorem indexProjectiveLocalObject_iff (W : Dᵒᵖ ⥤ SSet.{0}) [IsFibrant W] :
    Localization.localObject (indexProjectiveSegalLocalizingFamily F) W ↔
      Localization.localObject segalLocalizingFamily ((restrictIndex.{0, 0} F).obj W) := by
  letI := projectiveRestriction_isFibrant F W
  exact ⟨fun h ↦ ⟨inferInstance, (indexProjectiveSegalLocalizingFamily_iff F W).mp h.2⟩,
    fun h ↦ ⟨inferInstance, (indexProjectiveSegalLocalizingFamily_iff F W).mpr h.2⟩⟩

end

end DaggerModels.PartII.SegalLocalizers
