import DaggerModelsPartII.ReedyMaps
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Terminal relative matching maps

The relative Reedy matching map to the terminal diagram differs from the
absolute matching comparison only by the canonical terminal pullback
isomorphism. This statement is independent of any model structure.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerModels.PartII.ReedyTerminalMatching

noncomputable section

variable {C : Type u} [Category.{0} C] [HasLimitsOfSize.{0, 0} C]

/-- The terminal relative matching arrow is canonically the absolute
matching arrow, with the original degree-`n` source unchanged. -/
def terminalMatchingArrowIso (D : SimplexCategoryᵒᵖ ⥤ C) (n : ℕ) :
    Arrow.mk (relativeMatchingMap n (terminal.from D)) ≅
      Arrow.mk ((matchingComparison n).app D) := by
  let T := ⊤_ (SimplexCategoryᵒᵖ ⥤ C)
  let f : D ⟶ T := terminal.from D
  letI : PreservesLimit (Functor.empty.{0} _) (matchingFunctor (C := C) n) := by
    unfold matchingFunctor
    infer_instance
  have hT : IsTerminal ((matchingFunctor n).obj T) :=
    terminalIsTerminal.isTerminalObj (matchingFunctor n) T
  have hTn : IsTerminal (T.obj (op ⦋n⦌)) :=
    terminalIsTerminal.isTerminalObj ((evaluation _ C).obj (op ⦋n⦌)) T
  letI : IsIso ((matchingComparison n).app T) :=
    isIso_of_isTerminal hTn hT _
  let π := pullback.fst ((matchingFunctor n).map f)
    ((matchingComparison n).app T)
  letI : IsIso π := pullback_fst_iso_of_right_iso _ _
  have hπ : relativeMatchingMap n f ≫ π = (matchingComparison n).app D :=
    pullback.lift_fst _ _ _
  refine Arrow.isoMk (Iso.refl (D.obj (op ⦋n⦌))) (asIso π) ?_
  change 𝟙 (D.obj (op ⦋n⦌)) ≫ (matchingComparison n).app D =
    relativeMatchingMap n f ≫ π
  rw [Category.id_comp]
  exact hπ.symm

#print axioms terminalMatchingArrowIso

end

end DaggerModels.PartII.ReedyTerminalMatching
