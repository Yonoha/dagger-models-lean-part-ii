import DaggerModelsPartII.RestrictionInjectiveQuillen
import DaggerModelsPartII.ActualLocalizedQuillen
import DaggerModelsPartII.CofibrantUnit
import DaggerModelsPartII.WeakReflectionFromFibrant

/-!
# Quillen equivalence for the actual Part I change of index

Restriction preserves all localized weak equivalences. Reflection on fibrant
objects therefore extends to all arrows; the actual unit on cofibrant objects
then gives the native Quillen-equivalence mapping criterion.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra MorphismProperty DaggerModels

namespace DaggerModels.PartII.ActualLocalizedEquivalence

open SegalLocalizers ActualIndexProjectiveModel

noncomputable section

private local instance : ModelCategory ReverseDaggerSpace.{0} := projectiveSegalModel
private local instance : ModelCategory ActualSpace := actualSegalModel

private theorem reversalWeakClasses_eq :
    projectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences =
      injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences := by
  have hp := ProjectiveKanDiagram.localized_exactClasses ReverseSimplexᵒᵖ
    LocalizerIndex localizerArrow localizerArrow_mono
  have hi := InjectiveKanDiagram.localized_exactClasses ReverseSimplexᵒᵖ
    LocalizerIndex localizerArrow localizerArrow_mono
  exact hp.2.trans
    ((ProjectiveInjectiveComparison.localEquivalences_eq _ _).trans hi.2.symm)

/-- Restriction preserves all weak equivalences for the two actual
projective localizations appearing in the manuscript's adjunction. -/
theorem actualRestriction_preservesProjectiveWeak
    {X Y : ActualSpace} (f : X ⟶ Y)
    (hf : (weakEquivalences ActualSpace) f) :
    (weakEquivalences ReverseDaggerSpace.{0}) (actualRestriction.{0}.map f) := by
  change projectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences _
  rw [reversalWeakClasses_eq]
  exact RestrictionInjectiveQuillen.actualRestriction_preservesLocalizedProjectiveWeak f hf

/-- The already proved fibrant reflection extends to every arrow, because
restriction now preserves every localized weak equivalence. -/
theorem actualRestriction_reflectsProjectiveWeak
    {X Y : ActualSpace} (f : X ⟶ Y)
    (hf : (weakEquivalences ReverseDaggerSpace.{0}) (actualRestriction.{0}.map f)) :
    (weakEquivalences ActualSpace) f := by
  apply WeakReflectionFromFibrant.reflects_weakEquivalences actualRestriction
    (fun g hg => actualRestriction_preservesProjectiveWeak g hg) ?_ f hf
  intro A B hA hB g hg
  exact actualRestriction_reflectsLocalizedWeakEquivalences g hA hB hg

/-- Restriction detects exactly the projective-localized weak equivalences. -/
theorem actualRestriction_weakEquivalence_iff
    {X Y : ActualSpace} (f : X ⟶ Y) :
    WeakEquivalence (actualRestriction.{0}.map f) ↔ WeakEquivalence f := by
  simp only [weakEquivalence_iff]
  exact ⟨actualRestriction_reflectsProjectiveWeak f,
    actualRestriction_preservesProjectiveWeak f⟩

/-- The manuscript's actual left Kan extension and restriction form a
Quillen equivalence between the specified projective Segal localizations. -/
theorem actualLeftAdjunction_isQuillenEquivalence :
    @Adjunction.IsQuillenEquivalence ReverseDaggerSpace.{0} ActualSpace _ _
      projectiveSegalModel actualSegalModel actualLeftExtension.{0} actualRestriction.{0}
      actualLeftAdjunction.{0} := by
  refine { toIsQuillenAdjunction := actualLeftAdjunction_localized_isQuillen
           weakEquivalence_homEquiv_iff := ?_ }
  intro X Y hX _hY f
  have hunit := CofibrantUnit.actualUnit_trivial_of_localizedProjectiveCofibrant X hX
  haveI : WeakEquivalence ((actualLeftAdjunction.{0}).unit.app X) := by
    apply (weakEquivalence_iff _).mpr
    change projectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences _
    rw [reversalWeakClasses_eq]
    exact hunit.2
  rw [Adjunction.homEquiv_unit]
  exact (weakEquivalence_precomp_iff _ _).trans
    (actualRestriction_weakEquivalence_iff f)

end

end DaggerModels.PartII.ActualLocalizedEquivalence
