import DaggerModelsPartII.CharacteristicQuotient

/-!
# The boundary of a palindromic characteristic cell

The literal outer-face orbit inclusion is the complement of interior orbits.
Its image under the characteristic map is exactly the intersection with the
preceding length stage.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerModels.FreeInvolution
open DaggerModelsPartII.DaggerSimplexIndex
open DaggerModels.PartII.DaggerNerveLengthFiltration
open DaggerModels.PartII.FreeDaggerPathChains
open DaggerModels.PartII.CharacteristicInterior
open DaggerModels.PartII.CharacteristicOuterBoundary
open DaggerModels.PartII.CharacteristicQuotient
open DaggerModels.PartII.ReversalOuterFaceAction
open DaggerModels.PartII.ReversalOuterFaceSubobject
open DaggerModels.PartII.ReversalRepresentableFixedPoints
open DaggerModels.PartII.DiscreteBorelDiagram

namespace DaggerModels.PartII.CellBoundaryGeometry

noncomputable section

/-- The degree-zero component of the actual strict-orbit inclusion of the
outer-face subpresheaf. -/
def boundaryOrbitInclusionPoint (n : ℕ) (hn : 1 ≤ n) (k : ReverseSimplex) :
    BoundaryOrbit n hn k → RepresentableOrbit n k :=
  ((subsetStrictOrbitInclusion
    (yoneda.obj (⟨n⟩ : ReverseSimplex))
    (representableReversalIso n) (representableReversal_involutive n)
    (boundarySource n hn) (outerFace_invariant n hn)).app (op k)).app (op ⦋0⦌)

private theorem boundaryOrbitInclusionPoint_orbit (n : ℕ) (hn : 1 ≤ n)
    {k : ReverseSimplex} (φ : (boundarySource n hn).toFunctor.obj (op k)) :
    boundaryOrbitInclusionPoint n hn k
      (orbit _ _ φ) = orbitClass n φ.val := rfl

private theorem interior_flip_iff (n : ℕ) (hn : 1 ≤ n)
    {k : ReverseSimplex} (φ : k ⟶ (⟨n⟩ : ReverseSimplex)) :
    Interior (flip φ) ↔ Interior φ := by
  constructor
  · intro hflip
    by_contra hnot
    have hface := (mem_outerFace_iff_not_interior hn φ).mpr hnot
    have hface' := outerFace_invariant n hn (op k) φ hface
    change flip φ ∈ (outerFaceSubpresheafAt n hn).obj (op k) at hface'
    exact ((mem_outerFace_iff_not_interior hn (flip φ)).mp hface') hflip
  · intro hφ
    by_contra hnot
    have hface := (mem_outerFace_iff_not_interior hn (flip φ)).mpr hnot
    have hface' := outerFace_invariant n hn (op k) (flip φ) hface
    change flip (flip φ) ∈ (outerFaceSubpresheafAt n hn).obj (op k) at hface'
    have hface'' : φ ∈ (outerFaceSubpresheafAt n hn).obj (op k) := by
      simpa only [flip_flip] using hface'
    exact ((mem_outerFace_iff_not_interior hn φ).mp hface'') hφ

private theorem orbitClass_mem_interiorOrbit_iff (n : ℕ) (hn : 1 ≤ n)
    {k : ReverseSimplex} (φ : k ⟶ (⟨n⟩ : ReverseSimplex)) :
    orbitClass n φ ∈ InteriorOrbit n k ↔ Interior φ := by
  constructor
  · rintro ⟨ψ, hψ, heq⟩
    rcases Quotient.exact heq with h | h
    · simpa only [h] using hψ
    · rw [representable_valueEquiv_eq_flip] at h
      rw [h] at hψ
      exact (interior_flip_iff n hn φ).mp hψ
  · intro hφ
    exact ⟨φ, hφ, rfl⟩

/-- An ambient reversal orbit is on the literal outer-face boundary exactly
when it is not represented by an interior parameter. -/
theorem boundaryOrbitInclusionPoint_range_iff_not_interior
    (n : ℕ) (hn : 1 ≤ n) (k : ReverseSimplex)
    (r : RepresentableOrbit n k) :
    r ∈ Set.range (boundaryOrbitInclusionPoint n hn k) ↔
      r ∉ InteriorOrbit n k := by
  induction r using Quotient.inductionOn with
  | _ φ =>
    change orbitClass n φ ∈ Set.range (boundaryOrbitInclusionPoint n hn k) ↔
      orbitClass n φ ∉ InteriorOrbit n k
    rw [orbitClass_mem_interiorOrbit_iff n hn φ]
    constructor
    · rintro ⟨q, hq⟩
      induction q using Quotient.inductionOn with
      | _ ψ =>
        change orbitClass n ψ.val = orbitClass n φ at hq
        rcases Quotient.exact hq with h | h
        · exact (mem_outerFace_iff_not_interior hn φ).mp (h ▸ ψ.property)
        · rw [representable_valueEquiv_eq_flip] at h
          have hface := outerFace_invariant n hn (op k) ψ.val ψ.property
          change flip ψ.val ∈ (outerFaceSubpresheafAt n hn).obj (op k) at hface
          rw [h, flip_flip] at hface
          exact (mem_outerFace_iff_not_interior hn φ).mp hface
    · intro hnot
      let ψ : (boundarySource n hn).toFunctor.obj (op k) :=
        ⟨φ, (mem_outerFace_iff_not_interior hn φ).mpr hnot⟩
      refine ⟨orbit _ _ ψ, ?_⟩
      exact boundaryOrbitInclusionPoint_orbit n hn ψ

/-- A palindromic characteristic orbit lies in the preceding length stage
exactly when its parameter orbit comes from the literal outer-face boundary. -/
theorem stageCharacteristicOrbitMap_preceding_iff_boundary
    {m : ℕ} {a b : FreeDaggerSimplex m} (p : a ⟶ b)
    (hp : 1 ≤ letterLength p)
    (hpal : Arrow.mk p = CharacteristicComposite.daggerArrow (Arrow.mk p))
    (k : ReverseSimplex) (r : RepresentableOrbit (letterLength p) k) :
    (∃ y : (lengthFiltration m (letterLength p - 1)).toFunctor.obj (op k),
      (Subfunctor.homOfLe
        (lengthFiltration_mono m (Nat.sub_le (letterLength p) 1))).app (op k) y =
        stageCharacteristicOrbitMap p hpal k r) ↔
      r ∈ Set.range (boundaryOrbitInclusionPoint (letterLength p) hp k) := by
  induction r using Quotient.inductionOn with
  | _ φ =>
    rw [boundaryOrbitInclusionPoint_range_iff_not_interior]
    change (∃ y : (lengthFiltration m (letterLength p - 1)).toFunctor.obj (op k),
      (Subfunctor.homOfLe
        (lengthFiltration_mono m (Nat.sub_le (letterLength p) 1))).app (op k) y =
        stageCharacteristicOrbitMap p hpal k (orbitClass (letterLength p) φ)) ↔
      orbitClass (letterLength p) φ ∉ InteriorOrbit (letterLength p) k
    rw [orbitClass_mem_interiorOrbit_iff (letterLength p) hp φ]
    have hbound : totalLength k.len m
        ((DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
          (FreeDaggerSimplex m)).extensionMap φ (letterChain p)) ≤
          letterLength p :=
      (totalLength_extensionMap m φ (letterChain p)).trans_eq
        (totalLength_letterChain p)
    have hlen := characteristic_totalLength_eq_iff_interior p hp φ
    change (totalLength k.len m
      ((DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
        (FreeDaggerSimplex m)).extensionMap φ (letterChain p)) =
        letterLength p ↔ Interior φ) at hlen
    constructor
    · rintro ⟨y, hy⟩
      have hshort : totalLength k.len m
          ((DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
            (FreeDaggerSimplex m)).extensionMap φ (letterChain p)) ≤
            letterLength p - 1 := by
        have heq := congrArg Subtype.val hy
        change y.val = (characteristic p).app (op k) φ at heq
        rw [characteristic_app] at heq
        change y.val =
          (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
            (FreeDaggerSimplex m)).extensionMap φ (letterChain p) at heq
        rw [← heq]
        exact y.property
      intro hφ
      have hfull := hlen.mpr hφ
      omega
    · intro hnot
      have hshort : totalLength k.len m
          ((DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
            (FreeDaggerSimplex m)).extensionMap φ (letterChain p)) ≤
            letterLength p - 1 := by
        have hneq : totalLength k.len m
          ((DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
            (FreeDaggerSimplex m)).extensionMap φ (letterChain p)) ≠
              letterLength p := fun h => hnot (hlen.mp h)
        omega
      refine ⟨⟨(characteristic p).app (op k) φ, ?_⟩, ?_⟩
      · rw [characteristic_app]
        exact hshort
      · apply Subtype.ext
        rfl

end

end DaggerModels.PartII.CellBoundaryGeometry
