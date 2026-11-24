import DaggerModelsPartII.CharacteristicComposite
import DaggerModels.FreeInvolution

/-!
# Fixed-length unreduced word orbits for the native dagger nerve

A word retains its source and target in the arrow category. The orbit quotient
and its chosen representatives are the existing FreeInvolution construction.
-/

set_option autoImplicit false

open CategoryTheory DaggerModels
open DaggerModelsPartII.DaggerSimplexIndex

namespace DaggerModels.PartII.PathOrbitCells

open DaggerNerveLengthFiltration CharacteristicComposite

noncomputable section

/-- Whole unreduced words of exactly ℓ letters, with their endpoints. -/
def Word (m ℓ : ℕ) :=
  {p : Arrow (FreeDaggerSimplex m) // letterLength p.hom = ℓ}

/-- Dagger reverses a word without reducing any adjacent inverse letters. -/
def daggerWord {m ℓ : ℕ} (p : Word m ℓ) : Word m ℓ :=
  ⟨daggerArrow p.1, by
    change letterLength (dagger p.1.hom) = ℓ
    rw [letterLength_dagger]
    exact p.2⟩

/-- The fixed-length dagger action is involutive. -/
theorem daggerWord_involutive (m ℓ : ℕ) :
    Function.Involutive (daggerWord (m := m) (ℓ := ℓ)) := by
  intro p
  apply Subtype.ext
  exact daggerArrow_involutive m p.1

/-- The actual equivalence implementing whole-word dagger. -/
def daggerEquiv (m ℓ : ℕ) : Word m ℓ ≃ Word m ℓ where
  toFun := daggerWord
  invFun := daggerWord
  left_inv := daggerWord_involutive m ℓ
  right_inv := daggerWord_involutive m ℓ

/-- The existing quotient by equality or dagger of fixed-length words. -/
abbrev WordOrbit (m ℓ : ℕ) :=
  FreeInvolution.Orbit (daggerEquiv m ℓ) (daggerWord_involutive m ℓ)

/-- The quotient map to the word's dagger orbit. -/
def orbit {m ℓ : ℕ} (p : Word m ℓ) : WordOrbit m ℓ :=
  FreeInvolution.orbit (daggerEquiv m ℓ) (daggerWord_involutive m ℓ) p

/-- One chosen representative of each fixed-length word orbit. -/
def representative {m ℓ : ℕ} (r : WordOrbit m ℓ) : Word m ℓ :=
  FreeInvolution.representative (daggerEquiv m ℓ) (daggerWord_involutive m ℓ) r

/-- Every fixed-length word is its chosen representative or its dagger. -/
theorem representative_cover {m ℓ : ℕ} (p : Word m ℓ) :
    p = representative (orbit p) ∨ p = daggerWord (representative (orbit p)) :=
  FreeInvolution.representative_cover (daggerEquiv m ℓ)
    (daggerWord_involutive m ℓ) p

/-- Representatives equal up to dagger index the same orbit. -/
theorem representative_separated {m ℓ : ℕ} {r s : WordOrbit m ℓ}
    (h : representative r = representative s ∨
      representative r = daggerWord (representative s)) : r = s :=
  FreeInvolution.representative_separated (daggerEquiv m ℓ)
    (daggerWord_involutive m ℓ) h

/-- Being a dagger palindrome is an equality of whole words with endpoints. -/
def Palindromic {m ℓ : ℕ} (p : Word m ℓ) : Prop := daggerWord p = p

/-- A word and its dagger have the same palindrome status. -/
theorem palindromic_dagger_iff {m ℓ : ℕ} (p : Word m ℓ) :
    Palindromic (daggerWord p) ↔ Palindromic p := by
  change daggerWord (daggerWord p) = daggerWord p ↔ daggerWord p = p
  rw [daggerWord_involutive m ℓ]
  exact eq_comm

/-- Palindrome status depends only on the actual dagger orbit. -/
theorem palindromic_iff_of_orbit_eq {m ℓ : ℕ}
    {p q : Word m ℓ} (h : orbit p = orbit q) :
    Palindromic p ↔ Palindromic q := by
  have hrel : p = q ∨ p = daggerWord q := Quotient.exact h
  rcases hrel with hp | hp
  · rw [hp]
  · rw [hp]
    exact palindromic_dagger_iff q

/-- A word has the palindrome status of its chosen orbit representative. -/
theorem palindromic_iff_representative {m ℓ : ℕ} (p : Word m ℓ) :
    Palindromic p ↔ Palindromic (representative (orbit p)) := by
  rcases representative_cover p with h | h
  · conv_lhs => rw [h]
  · conv_lhs => rw [h]
    exact palindromic_dagger_iff _

/-- The palindrome status assigned to an orbit through its representative. -/
def OrbitPalindromic {m ℓ : ℕ} (r : WordOrbit m ℓ) : Prop :=
  Palindromic (representative r)

/-- The orbit status agrees with the status of every member. -/
theorem palindromic_iff_orbitPalindromic {m ℓ : ℕ} (p : Word m ℓ) :
    Palindromic p ↔ OrbitPalindromic (orbit p) :=
  palindromic_iff_representative p

/-- Two fixed-length words lie in the same orbit exactly when they are equal
or related by dagger. -/
theorem orbit_eq_iff {m ℓ : ℕ} (p q : Word m ℓ) :
    orbit p = orbit q ↔ p = q ∨ p = daggerWord q := by
  constructor
  · exact Quotient.exact
  · intro h
    change p = q ∨ p = (daggerEquiv m ℓ) q at h
    exact Quotient.sound h

@[simp] theorem orbit_dagger {m ℓ : ℕ} (p : Word m ℓ) :
    orbit (daggerWord p) = orbit p :=
  FreeInvolution.orbit_involution (daggerEquiv m ℓ)
    (daggerWord_involutive m ℓ) p

@[simp] theorem orbit_representative {m ℓ : ℕ} (r : WordOrbit m ℓ) :
    orbit (representative r) = r :=
  FreeInvolution.orbit_representative (daggerEquiv m ℓ)
    (daggerWord_involutive m ℓ) r

/-- Orbit indices for palindromic fixed-length words. -/
def PalOrbit (m ℓ : ℕ) :=
  {r : WordOrbit m ℓ // OrbitPalindromic r}

/-- Orbit indices for nonpalindromic fixed-length words. -/
def NonpalOrbit (m ℓ : ℕ) :=
  {r : WordOrbit m ℓ // ¬ OrbitPalindromic r}

/-- Every fixed-length word orbit belongs to exactly one palindrome class. -/
noncomputable def orbitSplit (m ℓ : ℕ) :
    WordOrbit m ℓ ≃ PalOrbit m ℓ ⊕ NonpalOrbit m ℓ := by
  classical
  refine {
    toFun := fun r =>
      if h : OrbitPalindromic r then Sum.inl ⟨r, h⟩ else Sum.inr ⟨r, h⟩
    invFun := fun x => x.elim Subtype.val Subtype.val
    left_inv := ?_
    right_inv := ?_ }
  · intro r
    by_cases h : OrbitPalindromic r <;> simp [h]
  · intro x
    rcases x with ⟨r, hr⟩ | ⟨r, hr⟩
    · simp [hr]
    · simp [hr]

end

end DaggerModels.PartII.PathOrbitCells
