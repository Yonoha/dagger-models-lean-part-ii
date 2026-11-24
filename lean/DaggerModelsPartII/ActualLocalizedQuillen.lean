import DaggerModelsPartII.ActualSegalLocalization
import DaggerModelsPartII.LocalizedQuillenDescent

/-!
# The localized change-of-index Quillen adjunction

The index is the actual Part I free dagger-simplex category, with all enriched
dagger functors as morphisms. The localizing families and model structures are
the fixed manuscript families constructed in `ActualSegalLocalization`.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra
open DaggerModels.PartII.SegalLocalizers
open DaggerModels.PartII.DaggerSimplexPartIIndex
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.ActualIndexProjectiveModel

noncomputable section

local instance actualBase : ModelCategory ActualSpace := modelCategory
local instance reversalBase : ModelCategory ReverseDaggerSpace.{0} :=
  ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ

/-- A localized actual-index fibrant object restricts to a localized reversal
fibrant object; the additional condition is levelwise Kan fibrancy on the actual index. -/
theorem actualSegalModel_isFibrant_iff_restriction (W : ActualSpace) :
    @IsFibrant ActualSpace _ actualSegalModel.categoryWithFibrations _ W ↔
      (∀ d, IsFibrant (W.obj d)) ∧
        @IsFibrant ReverseDaggerSpace.{0} _ projectiveSegalModel.categoryWithFibrations _
          (actualRestriction.{0}.obj W) := by
  rw [actualSegalModel_isFibrant_iff, projectiveSegalModel_isFibrant_iff]

/-- The exact restriction functor sends actual-index local objects to reversal local objects. -/
theorem actualRestriction_localObject (W : ActualSpace)
    (hW : Localization.localObject (functorialImageSRev actualU) W) :
    Localization.localObject segalLocalizingFamily (actualRestriction.{0}.obj W) := by
  letI := hW.1
  exact ⟨projectiveRestriction_isFibrant actualU W,
    (actualProjectiveLocality_iff W).mp hW.2⟩

/-- The manuscript's left Kan extension and restriction remain a Quillen
adjunction after localization at the resolved Segal and completeness families. -/
theorem actualLeftAdjunction_localized_isQuillen :
    @Adjunction.IsQuillenAdjunction ReverseDaggerSpace.{0} ActualSpace _ _
      projectiveSegalModel actualSegalModel actualLeftExtension.{0} actualRestriction.{0}
      actualLeftAdjunction.{0} := by
  have hC := ProjectiveKanDiagram.localized_exactClasses ReverseSimplexᵒᵖ LocalizerIndex
    localizerArrow localizerArrow_mono
  have hD := ProjectiveKanDiagram.localized_exactClasses ActualDaggerSimplexᵒᵖ LocalizerIndex
    actualImageLocalizer actualImageLocalizer_mono
  exact Localization.localizedQuillen_of_rightLocal
    (ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ) modelCategory
    segalLocalizingFamily (functorialImageSRev actualU)
    projectiveSegalModel actualSegalModel hC.1 hC.2 hD.1 hD.2
    actualLeftExtension.{0} actualRestriction.{0} actualLeftAdjunction.{0}
    actualLeftAdjunction_projective_isQuillen actualRestriction_localObject

/-- Restriction detects localized weak equivalences between localized fibrant
objects. The derived-unit argument is still needed for Quillen equivalence. -/
theorem actualRestriction_reflectsLocalizedWeakEquivalences
    {X Y : ActualSpace} (f : X ⟶ Y)
    (hX : @IsFibrant ActualSpace _ actualSegalModel.categoryWithFibrations _ X)
    (hY : @IsFibrant ActualSpace _ actualSegalModel.categoryWithFibrations _ Y)
    (hf : projectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
      (actualRestriction.{0}.map f)) :
    actualSegalModel.categoryWithWeakEquivalences.weakEquivalences f := by
  have hlocal := ProjectiveKanDiagram.localized_isFibrant_iff
    ActualDaggerSimplexᵒᵖ LocalizerIndex actualImageLocalizer actualImageLocalizer_mono
  rw [actualSegalModel_weakEquivalences]
  apply actualRestriction_reflectsLocalEquivalences f ((hlocal X).mp hX) ((hlocal Y).mp hY)
  have hc := (ProjectiveKanDiagram.localized_exactClasses ReverseSimplexᵒᵖ LocalizerIndex
    localizerArrow localizerArrow_mono).2
  exact hc ▸ hf

end

end DaggerModels.PartII.ActualIndexProjectiveModel
