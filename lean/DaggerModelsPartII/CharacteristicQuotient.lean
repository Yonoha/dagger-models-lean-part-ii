import DaggerModelsPartII.CharacteristicFiber
import DaggerModelsPartII.DiscreteBorelDiagram
import DaggerModelsPartII.C2InvolutionActions
import DaggerModelsPartII.ReversalOuterFaceQuotient

/-!
# Interior fibers and the literal orbit quotient of the characteristic map
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerModels.FreeInvolution
open DaggerModelsPartII.DaggerSimplexIndex
open DaggerModels.PartII.DaggerNerveLengthFiltration
open DaggerModels.PartII.FreeDaggerPathChains
open DaggerModels.PartII.CharacteristicInterior
open DaggerModels.PartII.CharacteristicComposite
open DaggerModels.PartII.CharacteristicFiber
open DaggerModels.PartII.ReversalRepresentableFixedPoints
open DaggerModels.PartII.ReversalOuterFaceAction
open DaggerModels.PartII.DiscreteBorelDiagram
open DaggerModels.PartII.SegalLocalizers
open DaggerModels.PartII.CharacteristicOuterBoundary
open DaggerModels.PartII.ReversalOuterFaceSubobject

namespace DaggerModels.PartII.CharacteristicQuotient

noncomputable section

/-- A fixed element of the representable flip cannot be interior in positive
length. The literal outer-face union contains every fixed point. -/
theorem flip_ne_self_of_interior {k : ReverseSimplex} {n : ℕ}
    (hn : 2 ≤ n) (φ : k ⟶ (⟨n⟩ : ReverseSimplex))
    (hφ : Interior φ) : flip φ ≠ φ := by
  intro hfixed
  have hface := outerFace_fixed n hn (op k) φ hfixed
  exact ((mem_outerFace_iff_not_interior (by omega : 1 ≤ n) φ).mp hface) hφ

/-- For a non-palindromic word, its characteristic map is injective on
interior parameters. -/
theorem characteristic_interior_injective_of_nonpal
    {m : ℕ} {a b : FreeDaggerSimplex m} (p : a ⟶ b)
    (hp : 1 ≤ letterLength p)
    (hnot : Arrow.mk p ≠ daggerArrow (Arrow.mk p))
    {k : ReverseSimplex}
    (φ ψ : k ⟶ (⟨letterLength p⟩ : ReverseSimplex))
    (hφ : Interior φ) (hψ : Interior ψ)
    (heq : (characteristic p).app (op k) φ =
      (characteristic p).app (op k) ψ) : φ = ψ := by
  rcases (characteristic_interior_fiber_iff p hp φ ψ hφ hψ).mp heq with h | ⟨hpal, _⟩
  · exact h
  · exact False.elim (hnot hpal)

/-- The chosen representable involution acts pointwise by the literal flip. -/
theorem representable_valueEquiv_eq_flip {k : ReverseSimplex} (n : ℕ)
    (φ : k ⟶ (⟨n⟩ : ReverseSimplex)) :
    valueEquiv (yoneda.obj (⟨n⟩ : ReverseSimplex))
      (representableReversalIso n) (op k) φ = flip φ := by
  rfl

/-- The pointwise strict orbit of the actual reversal representable. -/
abbrev RepresentableOrbit (n : ℕ) (k : ReverseSimplex) :=
  Orbit
    (valueEquiv (yoneda.obj (⟨n⟩ : ReverseSimplex))
      (representableReversalIso n) (op k))
    (valueInvolutive (yoneda.obj (⟨n⟩ : ReverseSimplex))
      (representableReversalIso n)
      (representableReversal_involutive n) (op k))

def orbitClass {k : ReverseSimplex} (n : ℕ)
    (φ : k ⟶ (⟨n⟩ : ReverseSimplex)) : RepresentableOrbit n k :=
  orbit _ _ φ

/-- The characteristic map of a palindromic typed arrow descends to the
existing strict involution orbit quotient, at every reversal-simplex value. -/
def characteristicOrbitMap
    {m : ℕ} {a b : FreeDaggerSimplex m} (p : a ⟶ b)
    (hpal : Arrow.mk p = daggerArrow (Arrow.mk p)) (k : ReverseSimplex) :
    RepresentableOrbit (letterLength p) k →
      (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
        (FreeDaggerSimplex m)).extension.obj (op k) :=
  Quotient.lift ((characteristic p).app (op k)) (by
    intro φ ψ h
    rcases h with h | h
    · exact congrArg ((characteristic p).app (op k)) h
    · rw [representable_valueEquiv_eq_flip] at h
      rw [h]
      exact characteristic_flip_of_palindrome p hpal ψ)

/-- The induced map separates interior orbits. -/
theorem characteristicOrbitMap_injective_on_interior
    {m : ℕ} {a b : FreeDaggerSimplex m} (p : a ⟶ b)
    (hp : 1 ≤ letterLength p)
    (hpal : Arrow.mk p = daggerArrow (Arrow.mk p))
    {k : ReverseSimplex}
    (φ ψ : k ⟶ (⟨letterLength p⟩ : ReverseSimplex))
    (hφ : Interior φ) (hψ : Interior ψ)
    (heq : characteristicOrbitMap p hpal k
        (orbitClass (letterLength p) φ) =
          characteristicOrbitMap p hpal k (orbitClass (letterLength p) ψ)) :
    orbitClass (letterLength p) φ = orbitClass (letterLength p) ψ := by
  change (characteristic p).app (op k) φ =
    (characteristic p).app (op k) ψ at heq
  rcases (characteristic_interior_fiber_iff p hp φ ψ hφ hψ).mp heq with h | ⟨_, h⟩
  · exact congrArg (orbitClass (letterLength p)) h
  · calc
      orbitClass (letterLength p) φ =
          orbitClass (letterLength p) (flip φ) := by
            change orbit _ _ φ = orbit _ _
              (valueEquiv (yoneda.obj (⟨letterLength p⟩ : ReverseSimplex))
                (representableReversalIso (letterLength p)) (op k) φ)
            exact (orbit_involution _ _ φ).symm
      _ = orbitClass (letterLength p) ψ := congrArg _ h.symm

/-- The subset of strict orbits represented by interior parameters. -/
def InteriorOrbit (n : ℕ) (k : ReverseSimplex) :
    Set (RepresentableOrbit n k) :=
  {r | ∃ φ : k ⟶ (⟨n⟩ : ReverseSimplex),
    Interior φ ∧ orbitClass n φ = r}

/-- The descended characteristic map is injective on the actual subset of
interior orbits of the representable flip. -/
theorem characteristicOrbitMap_injOn_interior
    {m : ℕ} {a b : FreeDaggerSimplex m} (p : a ⟶ b)
    (hp : 1 ≤ letterLength p)
    (hpal : Arrow.mk p = daggerArrow (Arrow.mk p))
    (k : ReverseSimplex) :
    Set.InjOn (characteristicOrbitMap p hpal k)
      (InteriorOrbit (letterLength p) k) := by
  intro r hr s hs heq
  obtain ⟨φ, hφ, rfl⟩ := hr
  obtain ⟨ψ, hψ, rfl⟩ := hs
  exact characteristicOrbitMap_injective_on_interior p hp hpal φ ψ hφ hψ heq

/-- The descended characteristic maps form one natural transformation from
the existing strict orbit diagram to the discrete native dagger nerve. -/
def characteristicQuotientMap
    {m : ℕ} {a b : FreeDaggerSimplex m} (p : a ⟶ b)
    (hpal : Arrow.mk p = daggerArrow (Arrow.mk p)) :
    strictOrbitDiagram
      (yoneda.obj (⟨letterLength p⟩ : ReverseSimplex))
      (representableReversalIso (letterLength p))
      (representableReversal_involutive (letterLength p)) ⟶
    discreteDagger.obj
      (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
        (FreeDaggerSimplex m)) where
  app c := (SimplicialObject.const (Type 0)).map
    (characteristicOrbitMap p hpal c.unop)
  naturality {c d} f := by
    apply NatTrans.ext
    funext q r
    induction r using Quotient.inductionOn with
    | _ φ =>
      change (characteristic p).app d
          ((yoneda.obj (⟨letterLength p⟩ : ReverseSimplex)).map f φ) =
        (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
          (FreeDaggerSimplex m)).extension.map f
          ((characteristic p).app c φ)
      exact congrFun ((characteristic p).naturality f) φ

/-- Pointwise quotient map with codomain the exact total-length stage. -/
def stageCharacteristicOrbitMap
    {m : ℕ} {a b : FreeDaggerSimplex m} (p : a ⟶ b)
    (hpal : Arrow.mk p = daggerArrow (Arrow.mk p)) (k : ReverseSimplex) :
    RepresentableOrbit (letterLength p) k →
      (lengthFiltration m (letterLength p)).toFunctor.obj (op k) :=
  Quotient.lift ((stageCharacteristic p).app (op k)) (by
    intro φ ψ h
    rcases h with h | h
    · exact congrArg ((stageCharacteristic p).app (op k)) h
    · rw [representable_valueEquiv_eq_flip] at h
      rw [h]
      apply Subtype.ext
      exact characteristic_flip_of_palindrome p hpal ψ)

/-- The palindromic characteristic map factors naturally through the
existing strict orbit diagram and lands in its exact length stage. -/
def stageCharacteristicQuotientMap
    {m : ℕ} {a b : FreeDaggerSimplex m} (p : a ⟶ b)
    (hpal : Arrow.mk p = daggerArrow (Arrow.mk p)) :
    strictOrbitDiagram
      (yoneda.obj (⟨letterLength p⟩ : ReverseSimplex))
      (representableReversalIso (letterLength p))
      (representableReversal_involutive (letterLength p)) ⟶
    C2InvolutionActions.discreteDiagram.obj
      (lengthFiltration m (letterLength p)).toFunctor where
  app c := (SimplicialObject.const (Type 0)).map
    (stageCharacteristicOrbitMap p hpal c.unop)
  naturality {c d} f := by
    apply NatTrans.ext
    funext q r
    induction r using Quotient.inductionOn with
    | _ φ =>
      change (stageCharacteristic p).app d
          ((yoneda.obj (⟨letterLength p⟩ : ReverseSimplex)).map f φ) =
        (lengthFiltration m (letterLength p)).toFunctor.map f
          ((stageCharacteristic p).app c φ)
      exact congrFun ((stageCharacteristic p).naturality f) φ

/-- Inclusion of the length stage recovers the full descended
characteristic map on the nose. -/
theorem stageCharacteristicQuotientMap_inclusion
    {m : ℕ} {a b : FreeDaggerSimplex m} (p : a ⟶ b)
    (hpal : Arrow.mk p = daggerArrow (Arrow.mk p)) :
    stageCharacteristicQuotientMap p hpal ≫
      C2InvolutionActions.discreteDiagram.map
        (lengthFiltration m (letterLength p)).ι =
      characteristicQuotientMap p hpal := by
  apply NatTrans.ext
  funext c
  apply NatTrans.ext
  funext q r
  induction r using Quotient.inductionOn with
  | _ φ => rfl

/-- The actual outer-face subpresheaf at a palindromic word's length. -/
abbrev boundarySource (n : ℕ) (hn : 1 ≤ n) :=
  outerFaceSubpresheafAt n hn

/-- Its inherited literal reversal action. -/
def boundaryAction (n : ℕ) (hn : 1 ≤ n) :
    (boundarySource n hn).toFunctor ≅ (boundarySource n hn).toFunctor :=
  subsetAction (yoneda.obj (⟨n⟩ : ReverseSimplex))
    (representableReversalIso n) (representableReversal_involutive n)
    (boundarySource n hn) (outerFace_invariant n hn)

/-- Pointwise strict orbit of the inherited outer-face action. -/
abbrev BoundaryOrbit (n : ℕ) (hn : 1 ≤ n) (k : ReverseSimplex) :=
  Orbit
    (valueEquiv (boundarySource n hn).toFunctor
      (boundaryAction n hn) (op k))
    (valueInvolutive (boundarySource n hn).toFunctor
      (boundaryAction n hn)
      (subsetAction_involutive
        (yoneda.obj (⟨n⟩ : ReverseSimplex))
        (representableReversalIso n) (representableReversal_involutive n)
        (boundarySource n hn) (outerFace_invariant n hn)) (op k))

/-- The boundary characteristic of a palindromic word descends to the
strict orbit of the literal outer-face union. -/
def boundaryCharacteristicOrbitMap
    {m : ℕ} {a b : FreeDaggerSimplex m} (p : a ⟶ b)
    (hp : 1 ≤ letterLength p)
    (hpal : Arrow.mk p = daggerArrow (Arrow.mk p)) (k : ReverseSimplex) :
    BoundaryOrbit (letterLength p) hp k →
      (lengthFiltration m (letterLength p - 1)).toFunctor.obj (op k) :=
  Quotient.lift ((boundaryCharacteristic p hp).app (op k)) (by
    intro φ ψ h
    rcases h with h | h
    · exact congrArg ((boundaryCharacteristic p hp).app (op k)) h
    · rw [h]
      apply Subtype.ext
      exact characteristic_flip_of_palindrome p hpal ψ.val)

/-- The quotient boundary attaching map is natural and lands in the
preceding total-length stage. -/
def boundaryCharacteristicQuotientMap
    {m : ℕ} {a b : FreeDaggerSimplex m} (p : a ⟶ b)
    (hp : 1 ≤ letterLength p)
    (hpal : Arrow.mk p = daggerArrow (Arrow.mk p)) :
    strictOrbitDiagram
      (boundarySource (letterLength p) hp).toFunctor
      (boundaryAction (letterLength p) hp)
      (subsetAction_involutive
        (yoneda.obj (⟨letterLength p⟩ : ReverseSimplex))
        (representableReversalIso (letterLength p))
        (representableReversal_involutive (letterLength p))
        (boundarySource (letterLength p) hp)
        (outerFace_invariant (letterLength p) hp)) ⟶
    C2InvolutionActions.discreteDiagram.obj
      (lengthFiltration m (letterLength p - 1)).toFunctor where
  app c := (SimplicialObject.const (Type 0)).map
    (boundaryCharacteristicOrbitMap p hp hpal c.unop)
  naturality {c d} f := by
    apply NatTrans.ext
    funext q r
    induction r using Quotient.inductionOn with
    | _ φ =>
      change (boundaryCharacteristic p hp).app d
          ((boundarySource (letterLength p) hp).toFunctor.map f φ) =
        (lengthFiltration m (letterLength p - 1)).toFunctor.map f
          ((boundaryCharacteristic p hp).app c φ)
      exact congrFun ((boundaryCharacteristic p hp).naturality f) φ

/-- The quotient boundary square commutes with the literal inclusion of
the preceding length stage into the current one. -/
theorem boundaryCharacteristicQuotient_square
    {m : ℕ} {a b : FreeDaggerSimplex m} (p : a ⟶ b)
    (hp : 1 ≤ letterLength p)
    (hpal : Arrow.mk p = daggerArrow (Arrow.mk p)) :
    boundaryCharacteristicQuotientMap p hp hpal ≫
      C2InvolutionActions.discreteDiagram.map
        (Subfunctor.homOfLe
          (lengthFiltration_mono m (Nat.sub_le (letterLength p) 1))) =
    subsetStrictOrbitInclusion
        (yoneda.obj (⟨letterLength p⟩ : ReverseSimplex))
        (representableReversalIso (letterLength p))
        (representableReversal_involutive (letterLength p))
        (boundarySource (letterLength p) hp)
        (outerFace_invariant (letterLength p) hp) ≫
      stageCharacteristicQuotientMap p hpal := by
  apply NatTrans.ext
  funext c
  apply NatTrans.ext
  funext q r
  induction r using Quotient.inductionOn with
  | _ φ =>
    apply Subtype.ext
    rfl

end

end DaggerModels.PartII.CharacteristicQuotient
