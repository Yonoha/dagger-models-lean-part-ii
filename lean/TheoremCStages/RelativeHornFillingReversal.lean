import OriginalHornFillingReversal
import OriginalInnerHornFillersReversal
import NativeInnerHornFactorization

/-!
# Relative horn lifting through the actual simplicial reversal

The existing horn and standard-simplex reversal isomorphisms identify the
literal horn inclusion with the inclusion at the reversed index. The base
map of a supplied lifting square is reversed as well. Consequently lifting
against the original horn for `p` is equivalent to lifting against the
reversed horn for `opFunctor.map p`; the resulting lift retains both original
equations, including its prescribed image in the base.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial
open DaggerOriginalStandardSimplexReversal DaggerOriginalHornReversal
open DaggerOriginalHornFillingReversal

universe u

namespace DaggerModels.PartII.RelativeHornFillingReversal

noncomputable section

/-- Reverse the entire lower simplex map of a relative horn square. -/
def reverseBaseMap {Y : SSet.{u}} (n : ℕ)
    (β : (Δ[n] : SSet.{u}) ⟶ Y) : (Δ[n] : SSet.{u}) ⟶ Y.op :=
  standardSimplexReversalInv n ≫ SSet.opFunctor.map β

/-- Both maps in the supplied square reverse together; in particular the
specified lower map remains part of the exact reversed equation. -/
theorem reverse_square {X Y : SSet.{u}} (p : X ⟶ Y)
    (n : ℕ) (i : Fin (n + 1))
    (φ : (Λ[n, i] : SSet.{u}) ⟶ X)
    (β : (Δ[n] : SSet.{u}) ⟶ Y)
    (h : φ ≫ p = Λ[n, i].ι ≫ β) :
    reverseHornMap n i φ ≫ SSet.opFunctor.map p =
      Λ[n, i.rev].ι ≫ reverseBaseMap n β := by
  dsimp only [reverseHornMap, reverseBaseMap]
  rw [Category.assoc, ← Functor.map_comp, h, Functor.map_comp,
    ← Category.assoc, hornReversalInv_comp_ι, Category.assoc]

/-- The literal native opposite of a horn inclusion is the actual horn at
the reversed vertex, including the ambient standard-simplex isomorphism. -/
def hornArrowIso (n : ℕ) (i : Fin (n + 1)) :
    Arrow.mk (SSet.opFunctor.map (Λ[n, i] : (Δ[n] : SSet.{u}).Subcomplex).ι) ≅
      Arrow.mk (Λ[n, i.rev] : (Δ[n] : SSet.{u}).Subcomplex).ι :=
  Arrow.isoMk (hornReversalIso n i) (standardSimplexReversalIso n)
    (hornReversalHom_comp_ι n i)

/-- Relative lifting is invariant under the exact horn reversal. The
adjunction transports the whole commuting square and its chosen lower map;
the arrow isomorphism transports both the horn and ambient simplex. -/
theorem horn_lifting_iff_reversed {X Y : SSet.{u}} (p : X ⟶ Y)
    (n : ℕ) (i : Fin (n + 1)) :
    HasLiftingProperty (Λ[n, i] : (Δ[n] : SSet.{u}).Subcomplex).ι p ↔
      HasLiftingProperty (Λ[n, i.rev] : (Δ[n] : SSet.{u}).Subcomplex).ι
        (SSet.opFunctor.map p) := by
  let adj := SSet.opEquivalence.{u}.toAdjunction
  let e : Arrow.mk (SSet.opFunctor.map (Λ[n, i.rev] : (Δ[n] : SSet.{u}).Subcomplex).ι) ≅
      Arrow.mk (Λ[n, i] : (Δ[n] : SSet.{u}).Subcomplex).ι := by
    have h := hornArrowIso.{u} n i.rev
    rw [Fin.rev_rev] at h
    exact h
  constructor
  · intro hp
    have hop : HasLiftingProperty
        (SSet.opFunctor.map (Λ[n, i.rev] : (Δ[n] : SSet.{u}).Subcomplex).ι) p :=
      (HasLiftingProperty.iff_of_arrow_iso_left e p).mpr hp
    exact (adj.hasLiftingProperty_iff
      (Λ[n, i.rev] : (Δ[n] : SSet.{u}).Subcomplex).ι p).mp hop
  · intro hp
    have hop : HasLiftingProperty
        (SSet.opFunctor.map (Λ[n, i.rev] : (Δ[n] : SSet.{u}).Subcomplex).ι) p :=
      (adj.hasLiftingProperty_iff
        (Λ[n, i.rev] : (Δ[n] : SSet.{u}).Subcomplex).ι p).mpr hp
    exact (HasLiftingProperty.iff_of_arrow_iso_left e p).mp hop

/-- A reversed-index relative lifting property supplies a filler for each
specified original square, retaining both `φ = ι ≫ σ` and `σ ≫ p = β`. -/
theorem relative_filling_of_reversed_lifting {X Y : SSet.{u}} (p : X ⟶ Y)
    (n : ℕ) (i : Fin (n + 1))
    (hrev : HasLiftingProperty (Λ[n, i.rev] : (Δ[n] : SSet.{u}).Subcomplex).ι
      (SSet.opFunctor.map p))
    (φ : (Λ[n, i] : SSet.{u}) ⟶ X)
    (β : (Δ[n] : SSet.{u}) ⟶ Y)
    (h : φ ≫ p = Λ[n, i].ι ≫ β) :
    ∃ σ : (Δ[n] : SSet.{u}) ⟶ X,
      φ = Λ[n, i].ι ≫ σ ∧ σ ≫ p = β := by
  haveI : HasLiftingProperty (Λ[n, i] : (Δ[n] : SSet.{u}).Subcomplex).ι p :=
    (horn_lifting_iff_reversed p n i).mpr hrev
  let sq : CommSq φ (Λ[n, i] : (Δ[n] : SSet.{u}).Subcomplex).ι p β := ⟨h⟩
  exact ⟨sq.lift, sq.fac_left.symm, sq.fac_right⟩

/-- Native inner fibrations remain inner fibrations after the original
simplicial reversal; the conclusion tests every literal relative inner horn. -/
theorem innerFibrations_op {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : DaggerNativeInnerHornFactorization.innerFibrations p) :
    DaggerNativeInnerHornFactorization.innerFibrations
      (SSet.opFunctor.map p) := by
  rw [DaggerNativeInnerHornFactorization.innerFibrations_iff] at hp ⊢
  intro n i h0 hn
  have hi := DaggerOriginalInnerHornFillersReversal.reverse_inner_index h0 hn
  have hrev := hp n i.rev hi.1 hi.2
  have h := (horn_lifting_iff_reversed p (n + 2) i.rev).mp hrev
  rw [Fin.rev_rev] at h
  exact h

#print axioms reverse_square
#print axioms horn_lifting_iff_reversed
#print axioms relative_filling_of_reversed_lifting
#print axioms innerFibrations_op

end

end DaggerModels.PartII.RelativeHornFillingReversal
