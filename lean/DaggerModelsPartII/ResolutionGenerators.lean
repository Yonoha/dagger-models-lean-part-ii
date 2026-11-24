import DaggerModelsPartII.ResolutionAdjunction
import DaggerModels.FreeBoundary
import Mathlib.CategoryTheory.MorphismProperty.IsSmall

/-!
# The maps used in the resolution localization

These are the maps of Part II, `cs.not.Gh`, using the actual Part I free
dagger functor and the actual external tensor. The final lemma compares the
collapse family with all simplex operators for a two-out-of-three property.
It does not construct or assume a Bousfield localization.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MorphismProperty

universe u

namespace DaggerModels.PartII

noncomputable section

/-- The two kinds of test object in `G_dagger`: free boundaries and free simplices. -/
def resolutionTestObject (n : ℕ) (simplex : Bool) : DaggerSSet.{u} :=
  freeDagger.obj (if simplex then Δ[n] else (SSet.boundary n).toSSet)

/-- The external tensor of the ordinary collapse `Δ[k] ⟶ Δ[0]` with `A`. -/
def tensorCollapse (A : DaggerSSet.{u}) (k : ℕ) :
    (externalTensor A).obj Δ[k] ⟶ (externalTensor A).obj Δ[0] :=
  (externalTensor A).map (SSet.stdSimplex.map (simplexCollapse (op ⦋k⦌)))

/-- The family `S_h` of Part II, with its nonzero index written as `k + 1`. -/
def resolutionGenerators : MorphismProperty ResolutionDiagram.{u} :=
  ofHoms (fun i : ℕ × Bool × ℕ ↦ tensorCollapse (resolutionTestObject i.1 i.2.1) (i.2.2 + 1))

/-- The resolution localization uses a small family of arrows. -/
instance resolutionGenerators_isSmall : IsSmall.{u} resolutionGenerators.{u} :=
  isSmall_ofHoms _

/-- Two-out-of-three reduces tests on all simplex operators to the nonzero collapses. -/
theorem tensorCollapseTests_iff_allOperators
    (A : DaggerSSet.{u}) (P : MorphismProperty ResolutionDiagram.{u})
    [P.HasTwoOutOfThreeProperty] [P.ContainsIdentities] :
    (∀ k : ℕ, P (tensorCollapse A (k + 1))) ↔
      (∀ (m n : ℕ) (f : ⦋m⦌ ⟶ ⦋n⦌),
        P ((externalTensor A).map (SSet.stdSimplex.map f))) := by
  constructor
  · intro h
    have hAll (k : ℕ) : P (tensorCollapse A k) := by
      cases k with
      | zero =>
        have hZero : simplexCollapse (op ⦋0⦌) = 𝟙 ⦋0⦌ :=
          SimplexCategory.isTerminalZero.hom_ext _ _
        rw [tensorCollapse, hZero, CategoryTheory.Functor.map_id SSet.stdSimplex, (externalTensor A).map_id]
        exact P.id_mem _
      | succ k => exact h k
    intro m n f
    apply P.of_postcomp _ (tensorCollapse A n) (hAll n)
    have hComp : f ≫ simplexCollapse (op ⦋n⦌) = simplexCollapse (op ⦋m⦌) :=
      SimplexCategory.isTerminalZero.hom_ext _ _
    rw [tensorCollapse, ← Functor.map_comp, ← Functor.map_comp, hComp]
    exact hAll m
  · intro h k
    exact h (k + 1) 0 (simplexCollapse (op ⦋k + 1⦌))

end

end DaggerModels.PartII
