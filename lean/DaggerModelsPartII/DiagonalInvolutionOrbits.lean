import DaggerModelsPartII.DiscreteOrbitSubobject
import Mathlib.Logic.Equiv.Prod

/-!
# Diagonal orbits with a free discrete factor

This is the set-level cancellation used in the pointwise Borel collapse.
The first factor is decomposed over its actual involution-orbit quotient;
the second factor may carry any involution, including one with fixed points.
-/

set_option autoImplicit false

universe u v w

namespace DaggerModels.PartII.DiagonalInvolutionOrbits

open DaggerModels.FreeInvolution

variable {X : Type u} {Y : Type v}
  (τ : X ≃ X) (hτ : Function.Involutive τ)
  (σ : Y ≃ Y) (hσ : Function.Involutive σ)

/-- The diagonal involution on a product. -/
def diagonal : X × Y ≃ X × Y := Equiv.prodCongr τ σ

include hτ hσ in
theorem diagonal_involutive : Function.Involutive (diagonal τ σ) := by
  rintro ⟨x, y⟩
  exact Prod.ext (hτ x) (hσ y)

/-- Strict diagonal orbits, with no freeness requirement on the second factor. -/
abbrev DiagonalOrbit := Orbit (diagonal τ σ) (diagonal_involutive τ hτ σ hσ)

variable (hfree : ∀ x, τ x ≠ x)

/-- Normalize a pair using the representative of the first factor's orbit. -/
noncomputable def normalize (p : X × Y) : Orbit τ hτ × Y :=
  let e := DaggerModels.FreeInvolution.equiv τ hτ hfree p.1
  (e.1, if e.2 then σ p.2 else p.2)

include hσ in
theorem normalize_diagonal (p : X × Y) :
    normalize τ hτ σ hfree (diagonal τ σ p) = normalize τ hτ σ hfree p := by
  rcases p with ⟨x, y⟩
  change (((equiv τ hτ hfree) (τ x)).1,
    if ((equiv τ hτ hfree) (τ x)).2 then σ (σ y) else σ y) =
      (((equiv τ hτ hfree) x).1, if ((equiv τ hτ hfree) x).2 then σ y else y)
  rw [DaggerModels.FreeInvolution.equiv_involution]
  cases (DaggerModels.FreeInvolution.equiv τ hτ hfree x).2
  · exact Prod.ext rfl (hσ y)
  · rfl

/-- Cancelling the free discrete factor leaves one copy of the second factor per orbit. -/
noncomputable def cancellation :
    DiagonalOrbit τ hτ σ hσ ≃ Orbit τ hτ × Y where
  toFun := Quotient.lift (normalize τ hτ σ hfree) (by
    intro p q hpq
    rcases hpq with h | h
    · exact congrArg _ h
    · rw [h, normalize_diagonal τ hτ σ hσ hfree])
  invFun p := orbit (diagonal τ σ) (diagonal_involutive τ hτ σ hσ)
    (representative τ hτ p.1, p.2)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ p =>
      rcases p with ⟨x, y⟩
      let e := DaggerModels.FreeInvolution.equiv τ hτ hfree
      have hx : assemble τ hτ (e x) = x := e.symm_apply_apply x
      change orbit _ _ (representative τ hτ (e x).1,
        if (e x).2 then σ y else y) = orbit _ _ (x, y)
      cases h : (e x).2
      · apply Quotient.sound
        apply Or.inl
        apply Prod.ext
        · simpa [assemble, h] using hx
        · rfl
      · apply Quotient.sound
        apply Or.inr
        apply Prod.ext
        · change representative τ hτ (e x).1 = τ x
          have hx' : τ (representative τ hτ (e x).1) = x := by
            simpa [assemble, h] using hx
          exact (hτ (representative τ hτ (e x).1)).symm.trans (congrArg τ hx')
        · rfl
  right_inv := by
    rintro ⟨r, y⟩
    have he : DaggerModels.FreeInvolution.equiv τ hτ hfree (representative τ hτ r) =
        (r, false) :=
      (DaggerModels.FreeInvolution.equiv τ hτ hfree).apply_symm_apply (r, false)
    change normalize τ hτ σ hfree (representative τ hτ r, y) = (r, y)
    simp [normalize, he]

@[simp] theorem cancellation_representative (r : Orbit τ hτ) (y : Y) :
    cancellation τ hτ σ hσ hfree
      (orbit (diagonal τ σ) (diagonal_involutive τ hτ σ hσ)
        (representative τ hτ r, y)) = (r, y) :=
  (cancellation τ hτ σ hσ hfree).apply_symm_apply (r, y)

/-- The orbit coordinate of the chosen free-action decomposition is the original quotient. -/
theorem freeEquiv_fst (x : X) :
    (DaggerModels.FreeInvolution.equiv τ hτ hfree x).1 = orbit τ hτ x := by
  let e := DaggerModels.FreeInvolution.equiv τ hτ hfree
  calc
    (e x).1 = orbit τ hτ (assemble τ hτ (e x)) := (orbit_assemble τ hτ (e x)).symm
    _ = orbit τ hτ x := congrArg (orbit τ hτ) (e.symm_apply_apply x)

/-- The projection from a diagonal orbit to the first factor's orbit. -/
def projection : DiagonalOrbit τ hτ σ hσ → Orbit τ hτ :=
  Quotient.lift (fun p : X × Y ↦ orbit τ hτ p.1) (by
    intro p q hpq
    rcases hpq with h | h
    · exact congrArg (fun p : X × Y ↦ orbit τ hτ p.1) h
    · apply Quotient.sound
      exact Or.inr (congrArg Prod.fst h))

@[simp] theorem cancellation_fst (q : DiagonalOrbit τ hτ σ hσ) :
    (cancellation τ hτ σ hσ hfree q).1 = projection τ hτ σ hσ q := by
  induction q using Quotient.inductionOn with
  | _ p => exact freeEquiv_fst τ hτ hfree p.1

variable {Z : Type w} (ω : Z ≃ Z) (hω : Function.Involutive ω)
  (f : Y → Z) (hf : ∀ y, f (σ y) = ω (f y))

/-- An equivariant map of second factors induces a map of strict diagonal orbits. -/
def secondMap : DiagonalOrbit τ hτ σ hσ → DiagonalOrbit τ hτ ω hω :=
  Quotient.map' (fun p : X × Y ↦ (p.1, f p.2)) (by
    intro p q hpq
    rcases hpq with h | h
    · exact Or.inl (congrArg (fun p : X × Y ↦ (p.1, f p.2)) h)
    · apply Or.inr
      change (p.1, f p.2) = (τ q.1, ω (f q.2))
      apply Prod.ext
      · exact congrArg (fun p : X × Y ↦ p.1) h
      · exact (congrArg f (congrArg (fun p : X × Y ↦ p.2) h)).trans (hf q.2))

/-- Cancellation is natural in every equivariant map of second factors. -/
theorem cancellation_secondMap (q : DiagonalOrbit τ hτ σ hσ) :
    cancellation τ hτ ω hω hfree (secondMap τ hτ σ hσ ω hω f hf q) =
      (cancellation τ hτ σ hσ hfree q).map id f := by
  induction q using Quotient.inductionOn with
  | _ p =>
    rcases p with ⟨x, y⟩
    change normalize τ hτ ω hfree (x, f y) =
      (normalize τ hτ σ hfree (x, y)).map id f
    dsimp only [normalize]
    cases (DaggerModels.FreeInvolution.equiv τ hτ hfree x).2
    · rfl
    · exact Prod.ext rfl (hf y).symm

end DaggerModels.PartII.DiagonalInvolutionOrbits
