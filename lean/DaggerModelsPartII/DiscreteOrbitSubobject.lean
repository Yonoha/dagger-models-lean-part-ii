import DaggerModels.FreeInvolution

/-!
# Orbits of an invariant subobject under an involution

These elementary set-level facts are the pointwise orbit inputs for the
discrete reversal-diagram Borel argument. They do not assert a model-category
statement about the quotient diagram.
-/

set_option autoImplicit false

universe u

namespace DaggerModels.PartII.DiscreteOrbitSubobject

open DaggerModels.FreeInvolution

variable {N : Type u} (τ : N ≃ N) (hτ : Function.Involutive τ)
variable (A : Set N) (hA : ∀ x ∈ A, τ x ∈ A)

/-- An invariant subset inherits the same involution. -/
def restrictedInvolution : {x : N // x ∈ A} ≃ {x : N // x ∈ A} where
  toFun x := ⟨τ x.1, hA x.1 x.2⟩
  invFun x := ⟨τ x.1, hA x.1 x.2⟩
  left_inv x := Subtype.ext (hτ x.1)
  right_inv x := Subtype.ext (hτ x.1)

@[simp] theorem restrictedInvolution_val (x : {x : N // x ∈ A}) :
    (restrictedInvolution τ hτ A hA x).1 = τ x.1 := rfl

theorem restrictedInvolution_involutive :
    Function.Involutive (restrictedInvolution τ hτ A hA) :=
  (restrictedInvolution τ hτ A hA).left_inv

/-- Inclusion of an invariant subset induces a map on strict orbit sets. -/
def orbitInclusion :
    Orbit (restrictedInvolution τ hτ A hA)
      (restrictedInvolution_involutive τ hτ A hA) →
      Orbit τ hτ :=
  Quotient.lift (fun x : {x : N // x ∈ A} ↦ orbit τ hτ x.1) (by
    intro x y hxy
    apply Quotient.sound
    rcases hxy with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h))

@[simp] theorem orbitInclusion_orbit (x : {x : N // x ∈ A}) :
    orbitInclusion τ hτ A hA
      (orbit (restrictedInvolution τ hτ A hA)
        (restrictedInvolution_involutive τ hτ A hA) x) =
      orbit τ hτ x.1 := rfl

/-- Distinct orbits in an invariant subset stay distinct in the ambient set. -/
theorem orbitInclusion_injective :
    Function.Injective (orbitInclusion τ hτ A hA) := by
  intro r s hrs
  induction r using Quotient.inductionOn with
  | _ x =>
    induction s using Quotient.inductionOn with
    | _ y =>
      change orbit τ hτ x.1 = orbit τ hτ y.1 at hrs
      apply Quotient.sound
      rcases Quotient.exact hrs with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)

/-- If every ambient fixed element lies in the invariant subset, the
complement carries a free involution. -/
theorem complement_free (hfixed : ∀ x, τ x = x → x ∈ A) :
    ∀ x : {x : N // x ∉ A}, τ x.1 ≠ x.1 := by
  intro x hx
  exact x.2 (hfixed x.1 hx)

/-- Invariance of a subset also makes its complement invariant. -/
theorem complement_invariant (hτ : Function.Involutive τ)
    (hA : ∀ x ∈ A, τ x ∈ A) :
    ∀ x, x ∉ A → τ x ∉ A := by
  intro x hx hmem
  apply hx
  have := hA (τ x) hmem
  simpa only [hτ x] using this

/-- The complement is a disjoint union of free two-element orbits when all
fixed elements have been included in the subobject. -/
noncomputable def complementOrbitEquiv (hfixed : ∀ x, τ x = x → x ∈ A) :
    {x : N // x ∉ A} ≃
      Orbit (restrictedInvolution τ hτ {x | x ∉ A}
        (complement_invariant τ A hτ hA))
        (restrictedInvolution_involutive τ hτ {x | x ∉ A}
          (complement_invariant τ A hτ hA)) × Bool :=
  FreeInvolution.equiv _ _ (by
    intro x hx
    exact complement_free τ A hfixed x (congrArg Subtype.val hx))

end DaggerModels.PartII.DiscreteOrbitSubobject
