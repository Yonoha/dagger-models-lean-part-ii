import DaggerModelsPartII.JTFrameZero
import Mathlib.CategoryTheory.Whiskering

/-!
# Projection augmentation of the dagger JT frame

The unique simplex operator `[k] ⟶ [0]` gives the manuscript's natural
augmentation from the full two-index dagger frame to its degree-zero value.
-/

set_option autoImplicit false

open CategoryTheory Simplicial DaggerModels

namespace DaggerModels.PartII.JTFrameAugmentation

open DaggerJTAdjunction DaggerJTFrameUnderlying JTFrameZero

noncomputable section

/-- Projection from each pair `(m,k)` to `(m,0)`, natural for every
reversal-simplex morphism in the first coordinate. -/
def projectionToZero :
    𝟭 DaggerIndex ⟶
      CategoryTheory.Prod.fst ReverseSimplex SimplexCategory ⋙ zeroSection where
  app p := (𝟙 p.1, SimplexCategory.isTerminalZero.from p.2)
  naturality p q f := by
    apply Prod.ext
    · rfl
    · exact SimplexCategory.isTerminalZero.hom_ext _ _

/-- At vertical degree zero, the projection operator is the identity. -/
theorem projectionToZero_zero (m : ReverseSimplex) :
    projectionToZero.app (m, ⦋0⦌) = 𝟙 (m, ⦋0⦌) := by
  apply Prod.ext
  · rfl
  · exact SimplexCategory.isTerminalZero.hom_ext _ _

/-- The actual projection augmentation of the two-variable dagger frame. -/
def frameAugmentation :
    frame ⟶
      CategoryTheory.Prod.fst ReverseSimplex SimplexCategory ⋙ reversalSimplex :=
  (Functor.leftUnitor frame).inv ≫
    Functor.whiskerRight projectionToZero frame ≫
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (CategoryTheory.Prod.fst ReverseSimplex SimplexCategory)
          frameZeroIso.hom

/-- The augmentation at degree zero is the chosen dagger frame
normalization, with no extra automorphism. -/
theorem frameAugmentation_zero (m : ReverseSimplex) :
    frameAugmentation.app (m, ⦋0⦌) = frameZeroIso.hom.app m := by
  simp [frameAugmentation, projectionToZero_zero]

end

end DaggerModels.PartII.JTFrameAugmentation
