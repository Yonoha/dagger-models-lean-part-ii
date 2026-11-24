import DaggerModelsPartII.DaggerNerveLengthOne
import DaggerModelsPartII.C2InvolutionActions
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Limits.Shapes.Preorder.TransfiniteCompositionOfShape

/-!
# The native dagger nerve is the actual colimit of total-length stages

The sequence starts at length one. Every chain is a finite unreduced word,
so it enters a finite stage. The inclusions are pointwise injective.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial DaggerModels
open DaggerModelsPartII.DaggerSimplexIndex
open DaggerModels.PartII.DaggerNerveLengthFiltration
open DaggerModels.PartII.C2InvolutionActions
open DaggerModels.PartII.SegalLocalizers

namespace DaggerModels.PartII.LengthFiltrationColimit

noncomputable section

/-- The literal length filtration, shifted to begin at `X₁`. -/
def lengthSequence (m : ℕ) : ℕ ⥤ (ReverseSimplexᵒᵖ ⥤ Type 0) where
  obj n := (lengthFiltration m (n + 1)).toFunctor
  map {n n'} f :=
    Subfunctor.homOfLe (lengthFiltration_mono m (Nat.succ_le_succ (leOfHom f)))
  map_id n := by
    ext c x
    rfl
  map_comp f g := by
    ext c x
    rfl

/-- Every stage includes into the full native dagger nerve. -/
def lengthSequenceInclusion (m : ℕ) :
    lengthSequence m ⟶
      (Functor.const ℕ).obj
        ((DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
          (FreeDaggerSimplex m)).extension) where
  app n := (lengthFiltration m (n + 1)).ι
  naturality n n' f := by
    ext c x
    rfl

/-- The full native nerve is the actual colimit of its length stages. -/
noncomputable def lengthSequenceIsColimit (m : ℕ) :
    IsColimit (Cocone.mk
      ((DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
        (FreeDaggerSimplex m)).extension)
      (lengthSequenceInclusion m)) := by
  apply evaluationJointlyReflectsColimits
  intro c
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    refine ⟨totalLength c.unop.len m x, ⟨x, ?_⟩, rfl⟩
    change totalLength c.unop.len m x ≤ totalLength c.unop.len m x + 1
    omega
  · intro j x y he
    exact ⟨j, 𝟙 j, Subtype.ext he⟩

/-- Apply the actual discrete simplicial-set embedding at every stage. -/
def discreteLengthSequence (m : ℕ) : ℕ ⥤ ReverseDaggerSpace.{0} :=
  lengthSequence m ⋙ discreteDiagram

/-- The discrete stages include into the discrete native dagger nerve. -/
def discreteLengthSequenceInclusion (m : ℕ) :
    discreteLengthSequence m ⟶
      (Functor.const ℕ).obj
        (discreteDagger.obj
          (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
            (FreeDaggerSimplex m))) where
  app n := discreteDiagram.map (lengthFiltration m (n + 1)).ι
  naturality n n' f := by
    ext c q x
    rfl

/-- The discrete native nerve is still the pointwise colimit of its
actual finite-length stages. -/
noncomputable def discreteLengthSequenceIsColimit (m : ℕ) :
    IsColimit (Cocone.mk
      (discreteDagger.obj
        (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
          (FreeDaggerSimplex m)))
      (discreteLengthSequenceInclusion m)) := by
  apply evaluationJointlyReflectsColimits
  intro c
  apply evaluationJointlyReflectsColimits
  intro q
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    refine ⟨totalLength c.unop.len m x, ⟨x, ?_⟩, rfl⟩
    change totalLength c.unop.len m x ≤ totalLength c.unop.len m x + 1
    omega
  · intro j x y he
    exact ⟨j, 𝟙 j, Subtype.ext he⟩

/-- The map from the first stage to the full discrete nerve is the
countable transfinite composite of the literal length-stage inclusions. -/
noncomputable def discreteLengthTransfiniteComposition (m : ℕ) :
    TransfiniteCompositionOfShape ℕ
      (discreteDiagram.map (lengthFiltration m 1).ι) where
  F := discreteLengthSequence m
  isoBot := Iso.refl _
  incl := discreteLengthSequenceInclusion m
  isColimit := discreteLengthSequenceIsColimit m
  fac := rfl

end

end DaggerModels.PartII.LengthFiltrationColimit
