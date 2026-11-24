import DaggerModelsPartII.DiagonalInvolutionOrbits
import Mathlib.Logic.Equiv.Sum

/-!
# Splitting diagonal orbits along an invariant subset

The split is natural in the second factor. No freeness or fixed-point
assumption is needed until the complement is subsequently cancelled.
-/

set_option autoImplicit false

universe u v

namespace DaggerModels.PartII.InvariantDiagonalOrbits

open DaggerModels.FreeInvolution DiagonalInvolutionOrbits DiscreteOrbitSubobject

noncomputable section

variable {X : Type u} {Y : Type v}
  (τ : X ≃ X) (hτ : Function.Involutive τ)
  (A : Set X) (hA : ∀ x ∈ A, τ x ∈ A)
  (σ : Y ≃ Y) (hσ : Function.Involutive σ)

abbrev subsetInvolution := restrictedInvolution τ hτ A hA
abbrev subsetInvolutive := restrictedInvolution_involutive τ hτ A hA
abbrev complementInvolution := restrictedInvolution τ hτ {x | x ∉ A}
  (complement_invariant τ A hτ hA)
abbrev complementInvolutive := restrictedInvolution_involutive τ hτ {x | x ∉ A}
  (complement_invariant τ A hτ hA)

/-- The equivariant subset inclusion induces the literal diagonal-orbit inclusion. -/
def subsetInclusion :
    DiagonalOrbit (subsetInvolution τ hτ A hA) (subsetInvolutive τ hτ A hA) σ hσ →
      DiagonalOrbit τ hτ σ hσ :=
  Quotient.map' (fun p : {x : X // x ∈ A} × Y ↦ (p.1.1, p.2)) (by
    intro p q hpq
    rcases hpq with h | h
    · exact Or.inl (congrArg (fun p : {x : X // x ∈ A} × Y ↦ (p.1.1, p.2)) h)
    · apply Or.inr
      change (p.1.1, p.2) = (τ q.1.1, σ q.2)
      exact Prod.ext (congrArg (fun p : {x : X // x ∈ A} × Y ↦ p.1.1) h)
        (congrArg (fun p : {x : X // x ∈ A} × Y ↦ p.2) h))

/-- The invariant complement has its own diagonal-orbit inclusion. -/
def complementInclusion :
    DiagonalOrbit (complementInvolution τ hτ A hA) (complementInvolutive τ hτ A hA) σ hσ →
      DiagonalOrbit τ hτ σ hσ :=
  subsetInclusion τ hτ {x | x ∉ A} (complement_invariant τ A hτ hA) σ hσ

/-- Select the summand before descending to the diagonal-orbit quotient. -/
def splitPair (p : X × Y) :
    DiagonalOrbit (subsetInvolution τ hτ A hA) (subsetInvolutive τ hτ A hA) σ hσ ⊕
      DiagonalOrbit (complementInvolution τ hτ A hA)
        (complementInvolutive τ hτ A hA) σ hσ := by
  classical
  exact if h : p.1 ∈ A then Sum.inl (orbit _ _ (⟨p.1, h⟩, p.2))
    else Sum.inr (orbit _ _ (⟨p.1, h⟩, p.2))

theorem splitPair_diagonal (p : X × Y) :
    splitPair τ hτ A hA σ hσ (diagonal τ σ p) = splitPair τ hτ A hA σ hσ p := by
  classical
  rcases p with ⟨x, y⟩
  by_cases hx : x ∈ A
  · simp only [splitPair, diagonal, Equiv.prodCongr_apply, Prod.map_apply,
      dif_pos hx, dif_pos (hA x hx)]
    exact congrArg Sum.inl (orbit_involution
      (diagonal (subsetInvolution τ hτ A hA) σ)
      (diagonal_involutive _ (subsetInvolutive τ hτ A hA) σ hσ) (⟨x, hx⟩, y))
  · have htx := complement_invariant τ A hτ hA x hx
    simp only [splitPair, diagonal, Equiv.prodCongr_apply, Prod.map_apply,
      dif_neg hx, dif_neg htx]
    exact congrArg Sum.inr (orbit_involution
      (diagonal (complementInvolution τ hτ A hA) σ)
      (diagonal_involutive _ (complementInvolutive τ hτ A hA) σ hσ) (⟨x, hx⟩, y))

/-- Diagonal orbits split as the disjoint union of subset and complement orbits. -/
def splitEquiv : DiagonalOrbit τ hτ σ hσ ≃
    DiagonalOrbit (subsetInvolution τ hτ A hA) (subsetInvolutive τ hτ A hA) σ hσ ⊕
      DiagonalOrbit (complementInvolution τ hτ A hA)
        (complementInvolutive τ hτ A hA) σ hσ where
  toFun := Quotient.lift (splitPair τ hτ A hA σ hσ) (by
    intro p q hpq
    rcases hpq with h | h
    · exact congrArg _ h
    · rw [h, splitPair_diagonal τ hτ A hA σ hσ])
  invFun := Sum.elim (subsetInclusion τ hτ A hA σ hσ)
    (complementInclusion τ hτ A hA σ hσ)
  left_inv := by
    classical
    intro q
    induction q using Quotient.inductionOn with
    | _ p =>
      change Sum.elim (subsetInclusion τ hτ A hA σ hσ)
        (complementInclusion τ hτ A hA σ hσ) (splitPair τ hτ A hA σ hσ p) =
          orbit _ _ p
      by_cases hx : p.1 ∈ A
      · simp only [splitPair, dif_pos hx]
        rfl
      · simp only [splitPair, dif_neg hx]
        rfl
  right_inv := by
    classical
    intro q
    rcases q with q | q
    · induction q using Quotient.inductionOn with
      | _ p =>
        change splitPair τ hτ A hA σ hσ (p.1.1, p.2) = _
        simp only [splitPair, dif_pos p.1.2]
        rfl
    · induction q using Quotient.inductionOn with
      | _ p =>
        change splitPair τ hτ A hA σ hσ (p.1.1, p.2) = _
        simp only [splitPair, dif_neg p.1.2]
        rfl

@[simp] theorem splitEquiv_subsetInclusion
    (q : DiagonalOrbit (subsetInvolution τ hτ A hA) (subsetInvolutive τ hτ A hA) σ hσ) :
    splitEquiv τ hτ A hA σ hσ (subsetInclusion τ hτ A hA σ hσ q) = Sum.inl q :=
  (splitEquiv τ hτ A hA σ hσ).apply_symm_apply (Sum.inl q)

@[simp] theorem splitEquiv_complementInclusion
    (q : DiagonalOrbit (complementInvolution τ hτ A hA)
      (complementInvolutive τ hτ A hA) σ hσ) :
    splitEquiv τ hτ A hA σ hσ (complementInclusion τ hτ A hA σ hσ q) = Sum.inr q :=
  (splitEquiv τ hτ A hA σ hσ).apply_symm_apply (Sum.inr q)

variable {Z : Type v} (ω : Z ≃ Z) (hω : Function.Involutive ω)
  (f : Y → Z) (hf : ∀ y, f (σ y) = ω (f y))

/-- The subset-complement split commutes with every equivariant map of second factors. -/
theorem splitEquiv_secondMap (q : DiagonalOrbit τ hτ σ hσ) :
    splitEquiv τ hτ A hA ω hω (secondMap τ hτ σ hσ ω hω f hf q) =
      Sum.map
        (secondMap (subsetInvolution τ hτ A hA) (subsetInvolutive τ hτ A hA)
          σ hσ ω hω f hf)
        (secondMap (complementInvolution τ hτ A hA) (complementInvolutive τ hτ A hA)
          σ hσ ω hω f hf)
        (splitEquiv τ hτ A hA σ hσ q) := by
  classical
  induction q using Quotient.inductionOn with
  | _ p =>
    change splitPair τ hτ A hA ω hω (p.1, f p.2) =
      Sum.map _ _ (splitPair τ hτ A hA σ hσ p)
    by_cases hx : p.1 ∈ A
    · simp only [splitPair, dif_pos hx]
      rfl
    · simp only [splitPair, dif_neg hx]
      rfl

end

end DaggerModels.PartII.InvariantDiagonalOrbits
