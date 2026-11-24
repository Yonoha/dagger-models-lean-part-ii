import DaggerModelsPartII.SubcomplexShellingWeak
import Lean.Elab.Tactic.Omega

/-!
# Finite-ordinal form of the original weak shelling theorem

A family indexed by `Fin (N+1)` is reindexed by clipping natural numbers
at `N`. Its initial unions and overlaps then match the exact finite
ordinal unions. This is only an index bridge to the existing shelling
theorem for one fixed map and the original Joyal weak predicate.
-/

set_option autoImplicit false

open CategoryTheory Limits Simplicial
open DaggerNativeJoyalMappingTest

namespace DaggerModels.PartII.FiniteOrdinalShellingWeak

noncomputable section

universe u

variable {X Y : SSet.{u}} (p : X ⟶ Y)

/-- The strict union of all cells preceding a specified finite-ordinal
index. At index zero the indexing type is empty. -/
def previous {N : ℕ} (F : Fin (N + 1) → X.Subcomplex)
    (t : Fin (N + 1)) : X.Subcomplex :=
  ⨆ s : {s : Fin (N + 1) // s.val < t.val}, F s.val

/-- Extend a finite family to natural numbers by repeating its last cell
after index `N`. -/
def natCell {N : ℕ} (F : Fin (N + 1) → X.Subcomplex)
    (i : ℕ) : X.Subcomplex :=
  F ⟨min i N, Nat.lt_succ_of_le (Nat.min_le_right i N)⟩

private theorem natCell_of_le {N : ℕ}
    (F : Fin (N + 1) → X.Subcomplex) (i : ℕ) (hi : i ≤ N) :
    natCell F i = F ⟨i, Nat.lt_succ_of_le hi⟩ := by
  have he :
      (⟨min i N, Nat.lt_succ_of_le (Nat.min_le_right i N)⟩ : Fin (N + 1)) =
        ⟨i, Nat.lt_succ_of_le hi⟩ :=
    Fin.ext (Nat.min_eq_left hi)
  exact congrArg F he

/-- The final natural-number prefix is exactly the full finite-ordinal
union, with no extra cell beyond `N`. -/
theorem initialUnion_natCell_eq_iSup {N : ℕ}
    (F : Fin (N + 1) → X.Subcomplex) :
    SubcomplexShellingWeak.initialUnion (natCell F) N = ⨆ t, F t := by
  change (Finset.range (N + 1)).sup (natCell F) = ⨆ t, F t
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    exact le_iSup (fun t : Fin (N + 1) ↦ F t)
      ⟨min i N, Nat.lt_succ_of_le (Nat.min_le_right i N)⟩
  · apply iSup_le
    intro t
    have hm : t.val ∈ Finset.range (N + 1) := Finset.mem_range.mpr t.isLt
    have hle : t.val ≤ N := Nat.le_of_lt_succ t.isLt
    have h := Finset.le_sup (f := natCell F) hm
    simpa only [natCell_of_le F t.val hle] using h

/-- A prefix ending at `n<N` is precisely the union indexed by the
finite ordinals strictly preceding `n+1`. -/
theorem initialUnion_natCell_eq_previous {N : ℕ}
    (F : Fin (N + 1) → X.Subcomplex) (n : ℕ) (hn : n < N) :
    SubcomplexShellingWeak.initialUnion (natCell F) n =
      previous F ⟨n + 1, Nat.succ_lt_succ hn⟩ := by
  change (Finset.range (n + 1)).sup (natCell F) =
    ⨆ s : {s : Fin (N + 1) // s.val < n + 1}, F s.val
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    have hi' : i < n + 1 := Finset.mem_range.mp hi
    have hiN : i ≤ N := by omega
    calc
      natCell F i = F ⟨i, Nat.lt_succ_of_le hiN⟩ := natCell_of_le F i hiN
      _ ≤ ⨆ s : {s : Fin (N + 1) // s.val < n + 1}, F s.val :=
        le_iSup (fun s : {s : Fin (N + 1) // s.val < n + 1} ↦ F s.val)
          ⟨⟨i, Nat.lt_succ_of_le hiN⟩, hi'⟩
  · apply iSup_le
    intro s
    have hs : s.val.val < n + 1 := s.property
    have hm : s.val.val ∈ Finset.range (n + 1) := Finset.mem_range.mpr hs
    have hle : s.val.val ≤ N := Nat.le_of_lt_succ s.val.isLt
    have h := Finset.le_sup (f := natCell F) hm
    simpa only [natCell_of_le F s.val.val hle] using h

private theorem iso_weak {A B : SSet.{u}} (f : A ⟶ B) [IsIso f] :
    weakCategoricalEquivalences f := by
  let e : Arrow.mk (𝟙 A) ≅ Arrow.mk f :=
    Arrow.isoMk (Iso.refl A) (asIso f) (by simp)
  exact weakCategoricalEquivalences.of_retract (Retract.ofIso e.symm)
    (weakCategoricalEquivalences.id_mem A)

/-- The finite-ordinal shelling criterion for one actual map `p`.
The zero-cell case requires only its own weak restriction; there is no
weak restriction from an empty source. -/
theorem weak_of_cover {N : ℕ} (F : Fin (N + 1) → X.Subcomplex)
    (hCover : (⨆ t, F t) = ⊤)
    (hCell : ∀ t : Fin (N + 1),
      weakCategoricalEquivalences ((F t).ι ≫ p))
    (hOverlap : ∀ t : Fin (N + 1), 0 < t.val →
      weakCategoricalEquivalences
        ((F t ⊓ previous F t).ι ≫ p)) :
    weakCategoricalEquivalences p := by
  have hNaturalCell : ∀ n ≤ N,
      weakCategoricalEquivalences (((natCell F n).ι) ≫ p) := by
    intro n hn
    rw [natCell_of_le F n hn]
    exact hCell ⟨n, Nat.lt_succ_of_le hn⟩
  have hNaturalOverlap : ∀ n < N,
      weakCategoricalEquivalences
        (((natCell F (n + 1) ⊓
          SubcomplexShellingWeak.initialUnion (natCell F) n).ι) ≫ p) := by
    intro n hn
    rw [natCell_of_le F (n + 1) (Nat.succ_le_of_lt hn),
      initialUnion_natCell_eq_previous F n hn]
    exact hOverlap ⟨n + 1, Nat.succ_lt_succ hn⟩ (by simp)
  have hPrefix := SubcomplexShellingWeak.prefix_weak p (natCell F) N
    hNaturalCell hNaturalOverlap
  have hTotal : SubcomplexShellingWeak.initialUnion (natCell F) N = ⊤ :=
    (initialUnion_natCell_eq_iSup F).trans hCover
  rw [hTotal] at hPrefix
  haveI : IsIso ((⊤ : X.Subcomplex).ι) := by
    change IsIso (SSet.Subcomplex.topIso X).hom
    infer_instance
  exact weakCategoricalEquivalences.of_precomp
    ((⊤ : X.Subcomplex).ι) p (iso_weak _) hPrefix

end

end DaggerModels.PartII.FiniteOrdinalShellingWeak
