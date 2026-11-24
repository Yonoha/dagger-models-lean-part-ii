import DaggerModelsPartII.BorelDiscreteOrbits
import DaggerModelsPartII.InvariantDiagonalOrbits
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# The invariant-subset coproduct decomposition of a discrete Borel construction

The two summands are defined before taking orbits. Their inclusions exhibit
the whole simplicial diagonal quotient as the actual categorical coproduct.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerModels.PartII.BorelDiscreteOrbits

open DaggerModels.FreeInvolution DiagonalInvolutionOrbits InvariantDiagonalOrbits

noncomputable section

variable (E : SSet.{u}) (σ : E ≅ E) (hσ : σ.hom ≫ σ.hom = 𝟙 E)
  {X : Type u} (τ : X ≃ X) (hτ : Function.Involutive τ)
  (A : Set X) (hA : ∀ x ∈ A, τ x ∈ A)

abbrev subsetBorel :=
  borel E σ hσ (subsetInvolution τ hτ A hA) (subsetInvolutive τ hτ A hA)
abbrev complementBorel :=
  borel E σ hσ (complementInvolution τ hτ A hA) (complementInvolutive τ hτ A hA)

/-- Inclusion of the Borel construction of the invariant subset. -/
def subsetBorelInclusion : subsetBorel E σ hσ τ hτ A hA ⟶ borel E σ hσ τ hτ where
  app n := subsetInclusion τ hτ A hA (degreeEquiv E σ n) (degree_involutive E σ hσ n)
  naturality n m f := by
    funext q
    induction q using Quotient.inductionOn with
    | _ p => rfl

/-- Inclusion of the Borel construction of the invariant complement. -/
def complementBorelInclusion : complementBorel E σ hσ τ hτ A hA ⟶ borel E σ hσ τ hτ where
  app n := complementInclusion τ hτ A hA (degreeEquiv E σ n) (degree_involutive E σ hσ n)
  naturality n m f := by
    funext q
    induction q using Quotient.inductionOn with
    | _ p => rfl

/-- Descend maps from the two orbit summands. -/
def splitDesc {Z : SSet.{u}} (f : subsetBorel E σ hσ τ hτ A hA ⟶ Z)
    (g : complementBorel E σ hσ τ hτ A hA ⟶ Z) : borel E σ hσ τ hτ ⟶ Z where
  app n q := Sum.elim (f.app n) (g.app n)
    (splitEquiv τ hτ A hA (degreeEquiv E σ n) (degree_involutive E σ hσ n) q)
  naturality n m α := by
    funext q
    change Sum.elim (f.app m) (g.app m)
      (splitEquiv τ hτ A hA (degreeEquiv E σ m) (degree_involutive E σ hσ m)
        (secondMap τ hτ (degreeEquiv E σ n) (degree_involutive E σ hσ n)
          (degreeEquiv E σ m) (degree_involutive E σ hσ m)
          (E.map α) (degree_comm E σ α) q)) = _
    rw [splitEquiv_secondMap]
    change _ = Z.map α (Sum.elim (f.app n) (g.app n)
      (splitEquiv τ hτ A hA (degreeEquiv E σ n) (degree_involutive E σ hσ n) q))
    cases splitEquiv τ hτ A hA (degreeEquiv E σ n) (degree_involutive E σ hσ n) q with
    | inl a => exact congrFun (f.naturality α) a
    | inr c => exact congrFun (g.naturality α) c

@[reassoc (attr := simp)] theorem subsetInclusion_splitDesc {Z : SSet.{u}}
    (f : subsetBorel E σ hσ τ hτ A hA ⟶ Z)
    (g : complementBorel E σ hσ τ hτ A hA ⟶ Z) :
    subsetBorelInclusion E σ hσ τ hτ A hA ≫ splitDesc E σ hσ τ hτ A hA f g = f := by
  apply NatTrans.ext
  funext n q
  change Sum.elim (f.app n) (g.app n)
    (splitEquiv τ hτ A hA (degreeEquiv E σ n) (degree_involutive E σ hσ n)
      (subsetInclusion τ hτ A hA (degreeEquiv E σ n) (degree_involutive E σ hσ n) q)) = _
  rw [splitEquiv_subsetInclusion]
  rfl

@[reassoc (attr := simp)] theorem complementInclusion_splitDesc {Z : SSet.{u}}
    (f : subsetBorel E σ hσ τ hτ A hA ⟶ Z)
    (g : complementBorel E σ hσ τ hτ A hA ⟶ Z) :
    complementBorelInclusion E σ hσ τ hτ A hA ≫ splitDesc E σ hσ τ hτ A hA f g = g := by
  apply NatTrans.ext
  funext n q
  change Sum.elim (f.app n) (g.app n)
    (splitEquiv τ hτ A hA (degreeEquiv E σ n) (degree_involutive E σ hσ n)
      (complementInclusion τ hτ A hA (degreeEquiv E σ n)
        (degree_involutive E σ hσ n) q)) = _
  rw [splitEquiv_complementInclusion]
  rfl

/-- The subset and complement inclusions exhibit the whole Borel quotient as their coproduct. -/
def splitIsColimit : IsColimit (BinaryCofan.mk
    (subsetBorelInclusion E σ hσ τ hτ A hA)
    (complementBorelInclusion E σ hσ τ hτ A hA)) :=
  BinaryCofan.isColimitMk
    (fun s ↦ splitDesc E σ hσ τ hτ A hA s.inl s.inr)
    (fun s ↦ subsetInclusion_splitDesc E σ hσ τ hτ A hA s.inl s.inr)
    (fun s ↦ complementInclusion_splitDesc E σ hσ τ hτ A hA s.inl s.inr) (by
      intro s m hmA hmC
      apply NatTrans.ext
      funext n q
      let e := splitEquiv τ hτ A hA (degreeEquiv E σ n) (degree_involutive E σ hσ n)
      obtain ⟨r, rfl⟩ := e.symm.surjective q
      rcases r with a | c
      · change m.app n (subsetInclusion τ hτ A hA (degreeEquiv E σ n)
          (degree_involutive E σ hσ n) a) = Sum.elim _ _ (e (e.symm (Sum.inl a)))
        rw [e.apply_symm_apply]
        exact congrFun (congr_app hmA n) a
      · change m.app n (complementInclusion τ hτ A hA (degreeEquiv E σ n)
          (degree_involutive E σ hσ n) c) = Sum.elim _ _ (e (e.symm (Sum.inr c)))
        rw [e.apply_symm_apply]
        exact congrFun (congr_app hmC n) c)

/-- The literal coproduct comparison, retaining the specified two inclusions. -/
def splitCoproductIso :
    (subsetBorel E σ hσ τ hτ A hA ⨿ complementBorel E σ hσ τ hτ A hA) ≅
      borel E σ hσ τ hτ :=
  (coprodIsCoprod _ _).coconePointUniqueUpToIso (splitIsColimit E σ hσ τ hτ A hA)

@[reassoc (attr := simp)] theorem inl_splitCoproductIso :
    coprod.inl ≫ (splitCoproductIso E σ hσ τ hτ A hA).hom =
      subsetBorelInclusion E σ hσ τ hτ A hA :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (coprodIsCoprod (subsetBorel E σ hσ τ hτ A hA) (complementBorel E σ hσ τ hτ A hA))
    (splitIsColimit E σ hσ τ hτ A hA) ⟨WalkingPair.left⟩

@[reassoc (attr := simp)] theorem inr_splitCoproductIso :
    coprod.inr ≫ (splitCoproductIso E σ hσ τ hτ A hA).hom =
      complementBorelInclusion E σ hσ τ hτ A hA :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (coprodIsCoprod (subsetBorel E σ hσ τ hτ A hA) (complementBorel E σ hσ τ hτ A hA))
    (splitIsColimit E σ hσ τ hτ A hA) ⟨WalkingPair.right⟩

end

end DaggerModels.PartII.BorelDiscreteOrbits
