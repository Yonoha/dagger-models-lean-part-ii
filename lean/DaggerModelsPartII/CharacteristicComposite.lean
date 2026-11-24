import DaggerModelsPartII.FreeDaggerPathChains
import DaggerModelsPartII.CharacteristicInterior
import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Characteristic-map composites retain the endpoints of the whole word

Words are objects of the native arrow category, so comparing a word with
its dagger is a well-typed equality that also records its source and target.
-/

set_option autoImplicit false

open CategoryTheory Opposite DaggerModels
open DaggerModelsPartII.DaggerSimplexIndex

namespace DaggerModels.PartII.CharacteristicComposite

open DaggerNerveLengthFiltration FreeDaggerPathChains

noncomputable section

/-- The composite of a native nerve chain, including its two endpoint objects. -/
def compositeArrow {n m : ℕ} (F : Fin (n + 1) ⥤ FreeDaggerSimplex m) :
    Arrow (FreeDaggerSimplex m) :=
  Arrow.mk (F.map (homOfLE (Fin.zero_le (Fin.last n))))

/-- Dagger reverses a whole word and exchanges its recorded endpoints. -/
def daggerArrow {m : ℕ} (p : Arrow (FreeDaggerSimplex m)) :
    Arrow (FreeDaggerSimplex m) := Arrow.mk (dagger p.hom)

/-- Whole-word dagger is involutive, with no cancellation of letters. -/
theorem daggerArrow_involutive (m : ℕ) :
    Function.Involutive (daggerArrow (m := m)) := by
  intro p
  obtain ⟨a, b, f, rfl⟩ := Arrow.mk_surjective p
  simp [daggerArrow]

/-- Recording a chain of letters as a whole word recovers the original
path and its source and target. -/
theorem compositeArrow_letterChain {m : ℕ} {a b : FreeDaggerSimplex m}
    (p : a ⟶ b) : compositeArrow (letterChain p) = Arrow.mk p := by
  have h := congrArg Arrow.mk (letterChain_composite p)
  simpa only [Arrow.arrow_mk_comp_eqToHom, Arrow.arrow_mk_eqToHom_comp] using h

private theorem arrowMk_eq_of_heq {C : Type*} [Category C]
    {a b a' b' : C} {f : a ⟶ b} {g : a' ⟶ b'}
    (ha : a = a') (hb : b = b') (hf : f ≍ g) : Arrow.mk f = Arrow.mk g := by
  cases ha
  cases hb
  exact congrArg Arrow.mk (eq_of_heq hf)

private theorem daggerMap_heq {n m : ℕ}
    (F : Fin (n + 1) ⥤ FreeDaggerSimplex m)
    {i j i' j' : Fin (n + 1)} (hi : i = i') (hj : j = j')
    (f : i ⟶ j) (g : i' ⟶ j') : dagger (F.map f) ≍ dagger (F.map g) := by
  cases hi
  cases hj
  exact heq_of_eq (congrArg (fun h ↦ dagger (F.map h)) (Subsingleton.elim f g))

/-- Monotone pullback preserving both endpoints preserves the whole
composite word, with its endpoints. -/
theorem compositeArrow_monotone_endpoints {n m : ℕ}
    (F : Fin (n + 1) ⥤ FreeDaggerSimplex m)
    {k : ReverseSimplex} (φ : k ⟶ (⟨n⟩ : ReverseSimplex))
    (hφ : Monotone φ.toFun)
    (hzero : φ.toFun 0 = 0) (hlast : φ.toFun (Fin.last k.len) = Fin.last n) :
    compositeArrow ((DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
      (FreeDaggerSimplex m)).extensionMap φ F) = compositeArrow F := by
  rw [DaggerSSet.extensionMap_monotone _ φ hφ]
  change Arrow.mk (F.map (homOfLE (hφ (Fin.zero_le (Fin.last k.len))))) =
    Arrow.mk (F.map (homOfLE (Fin.zero_le (Fin.last n))))
  exact arrowMk_eq_of_heq (congrArg F.obj hzero) (congrArg F.obj hlast)
    (freeChain_map_heq F hzero hlast _ _)

/-- Every monotone interior image of the characteristic map determines
the complete original word, including its endpoints. -/
theorem characteristic_composite_monotone {m : ℕ} {a b : FreeDaggerSimplex m}
    (p : a ⟶ b) {k : ReverseSimplex}
    (φ : k ⟶ (⟨letterLength p⟩ : ReverseSimplex)) (hφ : Monotone φ.toFun)
    (hzero : φ.toFun 0 = 0)
    (hlast : φ.toFun (Fin.last k.len) = Fin.last (letterLength p)) :
    compositeArrow ((characteristic p).app (op k) φ) = Arrow.mk p := by
  rw [characteristic_app]
  change compositeArrow ((DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
    (FreeDaggerSimplex m)).extensionMap φ (letterChain p)) = Arrow.mk p
  exact (compositeArrow_monotone_endpoints (letterChain p) φ hφ hzero hlast).trans
    (compositeArrow_letterChain p)

/-- Reversing a native chain daggers its whole composite word and exchanges
the endpoint objects recorded by the arrow category. -/
theorem compositeArrow_reversal {n m : ℕ}
    (F : Fin (n + 1) ⥤ FreeDaggerSimplex m) :
    compositeArrow ((DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
      (FreeDaggerSimplex m)).extensionMap
        (ReverseSimplex.reversal (⟨n⟩ : ReverseSimplex)) F) =
      daggerArrow (compositeArrow F) := by
  unfold compositeArrow daggerArrow
  refine arrowMk_eq_of_heq ?_ ?_ ?_
  · simpa using reversal_chain_object n m F 0
  · simpa using reversal_chain_object n m F (Fin.last n)
  · exact (reversal_chain_map_heq n m F (Fin.zero_le (Fin.last n))).trans
      (daggerMap_heq F (by simp) (by simp) _ _)

/-- Antitone pullback with opposite endpoints daggers the whole composite. -/
theorem compositeArrow_antitone_endpoints {n m : ℕ}
    (F : Fin (n + 1) ⥤ FreeDaggerSimplex m)
    {k : ReverseSimplex} (φ : k ⟶ (⟨n⟩ : ReverseSimplex))
    (hφ : Antitone φ.toFun)
    (hfirst : φ.toFun 0 = Fin.last n) (hfinal : φ.toFun (Fin.last k.len) = 0) :
    compositeArrow ((DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
      (FreeDaggerSimplex m)).extensionMap φ F) = daggerArrow (compositeArrow F) := by
  let α := ReverseSimplex.reversal k ≫ φ
  have hα : Monotone α.toFun := by
    intro i j hij
    exact hφ (Fin.rev_le_rev.mpr hij)
  have hzero : α.toFun 0 = 0 := by
    change φ.toFun (Fin.rev 0) = 0
    simpa using hfinal
  have hlast : α.toFun (Fin.last k.len) = Fin.last n := by
    change φ.toFun (Fin.rev (Fin.last k.len)) = Fin.last n
    simpa using hfirst
  have hmono := compositeArrow_monotone_endpoints F α hα hzero hlast
  let X := DaggerNativeOrdinaryDaggerNerveLift.daggerNerve (FreeDaggerSimplex m)
  have hx : daggerArrow (compositeArrow (X.extensionMap φ F)) = compositeArrow F := by
    rw [← compositeArrow_reversal]
    change compositeArrow (X.extensionMap (ReverseSimplex.reversal k)
      (X.extensionMap φ F)) = compositeArrow F
    rw [← X.extensionMap_comp]
    exact hmono
  have hd := congrArg daggerArrow hx
  simpa only [daggerArrow_involutive m (compositeArrow (X.extensionMap φ F))] using hd

/-- The composite of an antitone interior image is the dagger of the
original word, with both endpoints retained. -/
theorem characteristic_composite_antitone {m : ℕ} {a b : FreeDaggerSimplex m}
    (p : a ⟶ b) {k : ReverseSimplex}
    (φ : k ⟶ (⟨letterLength p⟩ : ReverseSimplex)) (hφ : Antitone φ.toFun)
    (hfirst : φ.toFun 0 = Fin.last (letterLength p))
    (hfinal : φ.toFun (Fin.last k.len) = 0) :
    compositeArrow ((characteristic p).app (op k) φ) =
      daggerArrow (Arrow.mk p) := by
  rw [characteristic_app]
  change compositeArrow ((DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
    (FreeDaggerSimplex m)).extensionMap φ (letterChain p)) = daggerArrow (Arrow.mk p)
  rw [compositeArrow_antitone_endpoints (letterChain p) φ hφ hfirst hfinal,
    compositeArrow_letterChain]

/-- An interior image determines the original whole word up to dagger. -/
theorem characteristic_interior_composite {m : ℕ} {a b : FreeDaggerSimplex m}
    (p : a ⟶ b) {k : ReverseSimplex}
    (φ : k ⟶ (⟨letterLength p⟩ : ReverseSimplex))
    (hφ : CharacteristicInterior.Interior φ) :
    compositeArrow ((characteristic p).app (op k) φ) = Arrow.mk p ∨
      compositeArrow ((characteristic p).app (op k) φ) = daggerArrow (Arrow.mk p) := by
  rcases hφ with ⟨hmono, hzero, hlast⟩ | ⟨hanti, hfirst, hfinal⟩
  · exact Or.inl (characteristic_composite_monotone p φ hmono hzero hlast)
  · exact Or.inr (characteristic_composite_antitone p φ hanti hfirst hfinal)

/-- Equal interior images of two paths force their whole words to agree
up to dagger, including their endpoints. Thus distinct word orbits have
disjoint interiors. -/
theorem interior_images_determine_wordOrbit {m : ℕ}
    {a b c d : FreeDaggerSimplex m} (p : a ⟶ b) (q : c ⟶ d)
    {k : ReverseSimplex}
    (φ : k ⟶ (⟨letterLength p⟩ : ReverseSimplex))
    (ψ : k ⟶ (⟨letterLength q⟩ : ReverseSimplex))
    (hφ : CharacteristicInterior.Interior φ) (hψ : CharacteristicInterior.Interior ψ)
    (heq : (characteristic p).app (op k) φ = (characteristic q).app (op k) ψ) :
    Arrow.mk p = Arrow.mk q ∨ Arrow.mk p = daggerArrow (Arrow.mk q) := by
  have hc := congrArg
    (fun F : Fin (k.len + 1) ⥤ FreeDaggerSimplex m ↦ compositeArrow F) heq
  rcases characteristic_interior_composite p φ hφ with hp | hp <;>
    rcases characteristic_interior_composite q ψ hψ with hq | hq
  · exact Or.inl (hp.symm.trans (hc.trans hq))
  · exact Or.inr (hp.symm.trans (hc.trans hq))
  · have h := congrArg daggerArrow (hp.symm.trans (hc.trans hq))
    exact Or.inr (by simpa only [daggerArrow_involutive m (Arrow.mk p)] using h)
  · have h := congrArg daggerArrow (hp.symm.trans (hc.trans hq))
    exact Or.inl (by
      simpa only [daggerArrow_involutive m (Arrow.mk p),
        daggerArrow_involutive m (Arrow.mk q)] using h)

end

end DaggerModels.PartII.CharacteristicComposite
