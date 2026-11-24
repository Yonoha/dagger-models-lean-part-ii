import DaggerModelsPartII.StrictFrameMappingFibration
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Kan fibrancy of an absolute strict frame mapping space

A Reedy fibrant opposite cosimplicial frame with weak structure maps has a
Kan mapping simplicial set into every fibrant coefficient. This is the
terminal-target instance of the checked relative frame mapping fibration.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite Simplicial
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.StrictFrameMappingKan

noncomputable section

variable {C : Type u} [Category.{0} C] [ModelCategory C]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]

private local instance : ModelCategory (SimplexCategoryᵒᵖ ⥤ Cᵒᵖ) :=
  simplicialReedyModelCategory Cᵒᵖ

/-- Absolute strict Hom into a fibrant coefficient is a Kan complex when
the opposite frame is Reedy fibrant and homotopically constant. -/
theorem strictMapping_obj_isFibrant (Z : C) [IsFibrant Z]
    (D : SimplexCategoryᵒᵖ ⥤ Cᵒᵖ) [IsFibrant D]
    (hD : ∀ {s t : SimplexCategoryᵒᵖ} (g : s ⟶ t),
      weakEquivalences Cᵒᵖ (D.map g)) :
    IsFibrant ((StrictFrameMappingWeak.strictMapping Z).obj D) := by
  let T := ⊤_ (SimplexCategoryᵒᵖ ⥤ Cᵒᵖ)
  letI : IsFibrant T := by
    letI : IsIso (terminal.from T) :=
      isIso_of_isTerminal terminalIsTerminal terminalIsTerminal _
    apply (isFibrant_iff_of_isTerminal (terminal.from T) terminalIsTerminal).mpr
    infer_instance
  have hTmaps : ∀ {s t : SimplexCategoryᵒᵖ} (g : s ⟶ t),
      weakEquivalences Cᵒᵖ (T.map g) := by
    intro s t g
    have hs : IsTerminal (T.obj s) :=
      terminalIsTerminal.isTerminalObj ((evaluation _ Cᵒᵖ).obj s) T
    have ht : IsTerminal (T.obj t) :=
      terminalIsTerminal.isTerminalObj ((evaluation _ Cᵒᵖ).obj t) T
    letI : IsIso (T.map g) := isIso_of_isTerminal hs ht _
    exact (weakEquivalences Cᵒᵖ).of_isIso _
  have hrel : reedyMatchingProperty (fibrations Cᵒᵖ) (terminal.from D) := by
    exact (fibration_iff _).mp
      ((isFibrant_iff_of_isTerminal (terminal.from D) terminalIsTerminal).mp
        inferInstance)
  have hf : Fibration
      ((StrictFrameMappingWeak.strictMapping Z).map (terminal.from D)) :=
    StrictFrameMappingFibration.strictMapping_map_fibration Z hD hTmaps
      (terminal.from D) hrel
  have htarget : IsTerminal ((StrictFrameMappingWeak.strictMapping Z).obj T) := by
    have : HasLimitsOfSize.{0, 0} Cᵒᵖ := inferInstance
    have : PreservesLimitsOfSize.{0, 0} (yoneda.obj Z) := inferInstance
    letI : PreservesLimitsOfSize.{0, 0}
        (StrictFrameMappingWeak.strictMapping Z) := by
      dsimp [StrictFrameMappingWeak.strictMapping]
      exact CategoryTheory.whiskeringRightPreservesLimits (yoneda.obj Z)
    exact terminalIsTerminal.isTerminalObj
      (StrictFrameMappingWeak.strictMapping Z) T
  exact (isFibrant_iff_of_isTerminal
    ((StrictFrameMappingWeak.strictMapping Z).map (terminal.from D)) htarget).mpr hf

#print axioms strictMapping_obj_isFibrant

end

end DaggerModels.PartII.StrictFrameMappingKan
