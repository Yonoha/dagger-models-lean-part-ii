import DaggerModelsPartII.JTParameterContraction
import DaggerModelsPartII.JTCylinderCEComparison

/-!
# Actual groupoid-parameter vertices are Kan trivial cofibrations

Use the retained actual augmentation to the terminal simplex. The original
free-groupoid simplex unit sends each standard vertex to the SAME specified
parameter vertex, so restricting a full parameter family keeps its endpoints.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTParameterVertexKan

noncomputable section

open GroupoidSimplex JTParameterContraction

/-- Any actual parameter vertex is monic because its source is the terminal simplex. -/
theorem vertex_mono (k : SimplexCategory) (j : Fin (k.len + 1)) :
    Mono (parameterVertex k j) :=
  SSet.stdSimplex.isTerminalObj₀.mono_from _

theorem vertex_cofibration (k : SimplexCategory) (j : Fin (k.len + 1)) :
    Cofibration (parameterVertex k j) := by
  have : Mono (parameterVertex k j) := vertex_mono k j
  exact (SSet.modelCategoryQuillen.cofibration_iff _).mpr inferInstance

/-- The SAME actual parameter vertex is Kan weak by the original augmentation. -/
theorem vertex_weak (k : SimplexCategory) (j : Fin (k.len + 1)) :
    WeakEquivalence (parameterVertex k j) := by
  have : WeakEquivalence (terminal.from (parameter.obj k)) :=
    (weakEquivalence_iff _).mpr (GroupoidSimplex.augmentation_trivialFibration k).2
  have : IsIso (terminal.from (Δ[0] : SSet.{0})) := by
    let e := SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso
      (terminalIsTerminal : IsTerminal (⊤_ SSet.{0}))
    have h : terminal.from (Δ[0] : SSet.{0}) = e.hom :=
      terminalIsTerminal.hom_ext _ _
    rw [h]
    infer_instance
  have h : parameterVertex k j ≫ terminal.from (parameter.obj k) =
      terminal.from (Δ[0] : SSet.{0}) := terminalIsTerminal.hom_ext _ _
  have : WeakEquivalence (parameterVertex k j ≫ terminal.from (parameter.obj k)) := by
    rw [h]
    infer_instance
  exact weakEquivalence_of_postcomp (parameterVertex k j) (terminal.from (parameter.obj k))

/-- Exact vertex calibration for the original free-groupoid simplex unit. -/
theorem simplexUnit_vertex (k : SimplexCategory) (j : Fin (k.len + 1)) :
    SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ k j) ≫
        JTCylinderCEComparison.simplexUnit.app k = parameterVertex k j := by
  letI : Quiver.IsThin (completion k) :=
    DaggerOriginalInitialCategoryCompletionThin.completionIsThin
      (0 : Fin (k.len + 1)) (Fin.isInitialZero _)
  apply SSet.yonedaEquiv.injective
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro i l f
  exact Subsingleton.elim _ _

end

end DaggerModels.PartII.JTParameterVertexKan
