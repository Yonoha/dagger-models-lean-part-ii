import DaggerModelsPartII.CharacteristicComposite

/-!
# Fibers of a path's characteristic map over interior parameters

Interior fibers are recovered from the unreduced word, with a second
parameter only when that word is fixed by the native dagger action.
-/

set_option autoImplicit false

open CategoryTheory Opposite DaggerModels
open DaggerModelsPartII.DaggerSimplexIndex

namespace DaggerModels.PartII.CharacteristicFiber

open DaggerNerveLengthFiltration FreeDaggerPathChains
open CharacteristicInterior CharacteristicLengthRecovery CharacteristicComposite
open ReversalRepresentableFixedPoints

noncomputable section

/-- Flipping the target exchanges the two interior orientations. -/
theorem interior_flip {k : ReverseSimplex} {n : ℕ}
    (φ : k ⟶ (⟨n⟩ : ReverseSimplex))
    (hφ : Interior φ) : Interior (flip φ) := by
  rcases hφ with ⟨hmono, hzero, hlast⟩ | ⟨hanti, hfirst, hfinal⟩
  · right
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij
      exact Fin.rev_le_rev.mpr (hmono hij)
    · change (φ.toFun 0).rev = Fin.last n
      simp only [hzero, Fin.rev_zero]
    · change (φ.toFun (Fin.last k.len)).rev = 0
      simp only [hlast, Fin.rev_last]
  · left
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij
      exact Fin.rev_le_rev.mpr (hanti hij)
    · change (φ.toFun 0).rev = 0
      simp only [hfirst, Fin.rev_last]
    · change (φ.toFun (Fin.last k.len)).rev = Fin.last n
      simp only [hfinal, Fin.rev_zero]

/-- The flip of a monotone interior parameter is antitone and has the
opposite endpoint configuration. -/
theorem flip_monotone_interior {k : ReverseSimplex} {n : ℕ}
    (φ : k ⟶ (⟨n⟩ : ReverseSimplex))
    (hmono : Monotone φ.toFun) (hzero : φ.toFun 0 = 0)
    (hlast : φ.toFun (Fin.last k.len) = Fin.last n) :
    Antitone (flip φ).toFun ∧ (flip φ).toFun 0 = Fin.last n ∧
      (flip φ).toFun (Fin.last k.len) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    exact Fin.rev_le_rev.mpr (hmono hij)
  · change (φ.toFun 0).rev = Fin.last n
    simp only [hzero, Fin.rev_zero]
  · change (φ.toFun (Fin.last k.len)).rev = 0
    simp only [hlast, Fin.rev_last]

/-- The flip of an antitone interior parameter is monotone and has the
original endpoint configuration. -/
theorem flip_antitone_interior {k : ReverseSimplex} {n : ℕ}
    (φ : k ⟶ (⟨n⟩ : ReverseSimplex))
    (hanti : Antitone φ.toFun)
    (hfirst : φ.toFun 0 = Fin.last n)
    (hfinal : φ.toFun (Fin.last k.len) = 0) :
    Monotone (flip φ).toFun ∧ (flip φ).toFun 0 = 0 ∧
      (flip φ).toFun (Fin.last k.len) = Fin.last n := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    exact Fin.rev_le_rev.mpr (hanti hij)
  · change (φ.toFun 0).rev = 0
    simp only [hfirst, Fin.rev_last]
  · change (φ.toFun (Fin.last k.len)).rev = Fin.last n
    simp only [hfinal, Fin.rev_zero]

private theorem characteristic_cast_of_eq {m : ℕ}
    {a : FreeDaggerSimplex m} {p q : a ⟶ a} (h : p = q) :
    (congrArg letterLength h).symm ▸ characteristic q = characteristic p := by
  cases h
  rfl

/-- A self-dagger loop has a characteristic map fixed by target reversal. -/
theorem characteristic_flip_of_self_dagger {m : ℕ}
    {a : FreeDaggerSimplex m} (p : a ⟶ a) (hp : p = dagger p)
    {k : ReverseSimplex}
    (φ : k ⟶ (⟨letterLength p⟩ : ReverseSimplex)) :
    (characteristic p).app (op k) (flip φ) =
      (characteristic p).app (op k) φ := by
  have hd := characteristic_dagger p
  have hcast : (letterLength_dagger p) ▸ characteristic (dagger p) =
      characteristic p := by
    exact characteristic_cast_of_eq hp
  have hfixed : yoneda.map (ReverseSimplex.reversal
      (⟨letterLength p⟩ : ReverseSimplex)) ≫ characteristic p = characteristic p := by
    exact hd.symm.trans hcast
  have heval := congrArg
    (fun η : yoneda.obj (⟨letterLength p⟩ : ReverseSimplex) ⟶
      (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
        (FreeDaggerSimplex m)).extension => η.app (op k) φ) hfixed
  simpa only [NatTrans.comp_app, yoneda_map_app,
    ReversalRepresentableFixedPoints.flip] using heval

/-- Arrow equality is the typed palindrome condition, including equality
of the two endpoint objects. -/
theorem characteristic_flip_of_palindrome {m : ℕ}
    {a b : FreeDaggerSimplex m} (p : a ⟶ b)
    (hpal : Arrow.mk p = daggerArrow (Arrow.mk p))
    {k : ReverseSimplex}
    (φ : k ⟶ (⟨letterLength p⟩ : ReverseSimplex)) :
    (characteristic p).app (op k) (flip φ) =
      (characteristic p).app (op k) φ := by
  have hab : a = b := by
    have h := congrArg Comma.left hpal
    simpa only [daggerArrow] using h
  cases hab
  have hp : p = dagger p := by
    apply (Arrow.mk_inj a a).mp
    simpa only [daggerArrow] using hpal
  exact characteristic_flip_of_self_dagger p hp φ

/-- The fiber calculation, isolating the native characteristic-map flip law
used to recover opposite-orientation parameters. -/
theorem characteristic_interior_fiber_iff_of_flip_law
    {m : ℕ} {a b : FreeDaggerSimplex m} (p : a ⟶ b)
    {k : ReverseSimplex}
    (φ ψ : k ⟶ (⟨letterLength p⟩ : ReverseSimplex))
    (hφ : Interior φ) (hψ : Interior ψ)
    (hflip : ∀ {j : ReverseSimplex}
      (θ : j ⟶ (⟨letterLength p⟩ : ReverseSimplex)),
      Arrow.mk p = daggerArrow (Arrow.mk p) →
        (characteristic p).app (op j) (flip θ) =
          (characteristic p).app (op j) θ) :
    (characteristic p).app (op k) φ =
      (characteristic p).app (op k) ψ ↔
        φ = ψ ∨
          (Arrow.mk p = daggerArrow (Arrow.mk p) ∧ ψ = flip φ) := by
  constructor
  · intro heq
    rcases hφ with ⟨hφmono, hφzero, hφlast⟩ |
      ⟨hφanti, hφfirst, hφfinal⟩
    · rcases hψ with ⟨hψmono, hψzero, hψlast⟩ |
        ⟨hψanti, hψfirst, hψfinal⟩
      · exact Or.inl (characteristic_monotone_injective p φ ψ
          hφmono hψmono hφzero hψzero heq)
      · have hpal : Arrow.mk p = daggerArrow (Arrow.mk p) := by
          calc
            Arrow.mk p = compositeArrow ((characteristic p).app (op k) φ) :=
              (characteristic_composite_monotone p φ hφmono hφzero hφlast).symm
            _ = compositeArrow ((characteristic p).app (op k) ψ) :=
              congrArg compositeArrow heq
            _ = daggerArrow (Arrow.mk p) :=
              characteristic_composite_antitone p ψ hψanti hψfirst hψfinal
        have hf := flip_monotone_interior φ hφmono hφzero hφlast
        have hχ : (characteristic p).app (op k) ψ =
            (characteristic p).app (op k) (flip φ) :=
          heq.symm.trans (hflip φ hpal).symm
        exact Or.inr ⟨hpal, characteristic_antitone_injective p ψ (flip φ)
          hψanti hf.1 hψfinal hf.2.2 hχ⟩
    · rcases hψ with ⟨hψmono, hψzero, hψlast⟩ |
        ⟨hψanti, _, hψfinal⟩
      · have hpal : Arrow.mk p = daggerArrow (Arrow.mk p) := by
          symm
          calc
            daggerArrow (Arrow.mk p) =
                compositeArrow ((characteristic p).app (op k) φ) :=
              (characteristic_composite_antitone p φ hφanti hφfirst hφfinal).symm
            _ = compositeArrow ((characteristic p).app (op k) ψ) :=
              congrArg compositeArrow heq
            _ = Arrow.mk p :=
              characteristic_composite_monotone p ψ hψmono hψzero
                hψlast
        have hf := flip_antitone_interior φ hφanti hφfirst hφfinal
        have hχ : (characteristic p).app (op k) ψ =
            (characteristic p).app (op k) (flip φ) :=
          heq.symm.trans (hflip φ hpal).symm
        exact Or.inr ⟨hpal, characteristic_monotone_injective p ψ (flip φ)
          hψmono hf.1 hψzero hf.2.1 hχ⟩
      · exact Or.inl (characteristic_antitone_injective p φ ψ
          hφanti hψanti hφfinal hψfinal heq)
  · rintro (heq | ⟨hpal, hψflip⟩)
    · rw [heq]
    · rw [hψflip]
      exact (hflip φ hpal).symm

/-- The exact interior fiber relation for an arbitrary positive-length
unreduced path. The palindrome condition is equality of native arrow objects,
so it includes equality of endpoint objects. -/
theorem characteristic_interior_fiber_iff
    {m : ℕ} {a b : FreeDaggerSimplex m} (p : a ⟶ b)
    (_hp : 1 ≤ letterLength p) {k : ReverseSimplex}
    (φ ψ : k ⟶ (⟨letterLength p⟩ : ReverseSimplex))
    (hφ : Interior φ) (hψ : Interior ψ) :
    (characteristic p).app (op k) φ =
      (characteristic p).app (op k) ψ ↔
        φ = ψ ∨
          (Arrow.mk p = daggerArrow (Arrow.mk p) ∧ ψ = flip φ) := by
  exact characteristic_interior_fiber_iff_of_flip_law p φ ψ hφ hψ
    (fun θ hpal => characteristic_flip_of_palindrome p hpal θ)

end

end DaggerModels.PartII.CharacteristicFiber
