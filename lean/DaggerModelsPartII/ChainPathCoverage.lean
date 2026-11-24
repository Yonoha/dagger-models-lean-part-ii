import DaggerModelsPartII.CharacteristicComposite
import DaggerModelsPartII.CharacteristicLengthRecovery
import DaggerModelsPartII.PathPrefixUniqueness

/-!
# Coverage of native chains by letter-word characteristic maps
-/

set_option autoImplicit false

open CategoryTheory Opposite DaggerModels
open DaggerModelsPartII.DaggerSimplexIndex

namespace DaggerModels.PartII.ChainPathCoverage

open DaggerNerveLengthFiltration FreeDaggerPathChains
open CharacteristicComposite CharacteristicLengthRecovery
open PathPrefixUniqueness

noncomputable section

private theorem factors_arrow_eq {m : ℕ}
    {a b c a' b' c' : FreeDaggerSimplex m}
    (p : a ⟶ b) (q : b ⟶ c) (p' : a' ⟶ b') (q' : b' ⟶ c')
    (hcomp : Arrow.mk (p ≫ q) = Arrow.mk (p' ≫ q'))
    (hlen : letterLength p = letterLength p') :
    Arrow.mk p = Arrow.mk p' ∧ Arrow.mk q = Arrow.mk q' := by
  obtain ⟨ha, hc, hwhole⟩ := (Arrow.mk_eq_mk_iff _ _).mp hcomp
  cases ha
  cases hc
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hwhole
  have hp : Quiver.Path.comp p q = Quiver.Path.comp p' q' := hwhole
  obtain ⟨hb, hpre, hsuf⟩ := factors_heq_of_comp_eq_of_length_eq
    p q p' q' hp hlen
  have hbb : b = b' := by
    cases b with | mk bv =>
      cases b' with | mk bw =>
        exact congrArg FreeDaggerSimplex.mk hb
  cases hbb
  exact ⟨congrArg Arrow.mk (eq_of_heq hpre),
    congrArg Arrow.mk (eq_of_heq hsuf)⟩

private theorem right_arrow_eq_of_prefix_and_whole {m : ℕ}
    {a b c a' b' c' : FreeDaggerSimplex m}
    (p : a ⟶ b) (q : b ⟶ c) (p' : a' ⟶ b') (q' : b' ⟶ c')
    (hpre : Arrow.mk p = Arrow.mk p')
    (hwhole : Arrow.mk (p ≫ q) = Arrow.mk (p' ≫ q')) :
    Arrow.mk q = Arrow.mk q' := by
  obtain ⟨ha, hb, hp⟩ := (Arrow.mk_eq_mk_iff _ _).mp hpre
  obtain ⟨_, hc, hcomp⟩ := (Arrow.mk_eq_mk_iff _ _).mp hwhole
  cases ha
  cases hb
  cases hc
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hp hcomp
  subst p'
  exact congrArg Arrow.mk (Quiver.Path.comp_injective_right p hcomp)

private theorem prefix_factor {k m : ℕ}
    (F : Fin (k + 1) ⥤ FreeDaggerSimplex m) (i : Fin (k + 1)) :
    Arrow.mk (F.map (homOfLE (Fin.zero_le i)) ≫
      F.map (homOfLE (Fin.le_last i))) = compositeArrow F := by
  unfold compositeArrow
  rw [← F.map_comp]
  congr 1

private theorem prefix_interval_factor {k m : ℕ}
    (F : Fin (k + 1) ⥤ FreeDaggerSimplex m)
    {i j : Fin (k + 1)} (hij : i ≤ j) :
    F.map (homOfLE (Fin.zero_le i)) ≫ F.map (homOfLE hij) =
      F.map (homOfLE (Fin.zero_le j)) := by
  rw [← F.map_comp]
  congr 1

/-- Equal full words and equal prefix lengths determine the whole native chain. -/
theorem chain_eq_of_compositeArrow_eq_and_prefixLengths {k m : ℕ}
    (F G : Fin (k + 1) ⥤ FreeDaggerSimplex m)
    (hwhole : compositeArrow F = compositeArrow G)
    (hlen : ∀ i : Fin (k + 1),
      letterLength (F.map (homOfLE (Fin.zero_le i))) =
        letterLength (G.map (homOfLE (Fin.zero_le i)))) : F = G := by
  have hprefix (i : Fin (k + 1)) :
      Arrow.mk (F.map (homOfLE (Fin.zero_le i))) =
        Arrow.mk (G.map (homOfLE (Fin.zero_le i))) := by
    exact (factors_arrow_eq
      (F.map (homOfLE (Fin.zero_le i))) (F.map (homOfLE (Fin.le_last i)))
      (G.map (homOfLE (Fin.zero_le i))) (G.map (homOfLE (Fin.le_last i)))
      (by simpa only [prefix_factor F i, prefix_factor G i] using hwhole)
      (hlen i)).1
  have hobj : ∀ i : Fin (k + 1), F.obj i = G.obj i := by
    intro i
    exact congrArg Comma.right (hprefix i)
  apply ComposableArrows.ext hobj
  intro i hi
  let ii : Fin k := ⟨i, hi⟩
  have hArrow :
      Arrow.mk (F.map (homOfLE (Fin.castSucc_le_succ ii))) =
        Arrow.mk (G.map (homOfLE (Fin.castSucc_le_succ ii))) := by
    apply right_arrow_eq_of_prefix_and_whole
      (F.map (homOfLE (Fin.zero_le ii.castSucc)))
      (F.map (homOfLE (Fin.castSucc_le_succ ii)))
      (G.map (homOfLE (Fin.zero_le ii.castSucc)))
      (G.map (homOfLE (Fin.castSucc_le_succ ii)))
      (hprefix ii.castSucc)
    simpa only [prefix_interval_factor F (Fin.castSucc_le_succ ii),
      prefix_interval_factor G (Fin.castSucc_le_succ ii)] using
        hprefix ii.succ
  obtain ⟨ha, hb, hmap⟩ := (Arrow.mk_eq_mk_iff _ _).mp hArrow
  exact hmap

/-- The unreduced path obtained by composing every arrow in a native chain. -/
def fullPath {k m : ℕ} (F : Fin (k + 1) ⥤ FreeDaggerSimplex m) :
    F.obj 0 ⟶ F.obj (Fin.last k) :=
  F.map (homOfLE (Fin.zero_le (Fin.last k)))

/-- The position of a chain vertex inside the letter chain of its whole path. -/
def prefixParameter {k m : ℕ}
    (F : Fin (k + 1) ⥤ FreeDaggerSimplex m) :
    (⟨k⟩ : ReverseSimplex) ⟶
      (⟨letterLength (fullPath F)⟩ : ReverseSimplex) where
  toFun i := ⟨letterLength (F.map (homOfLE (Fin.zero_le i))), by
    have hi := intervalLength_le_total F (Fin.zero_le i)
    rw [totalLength_eq_composite] at hi
    exact Nat.lt_succ_of_le hi⟩
  monotone_or_antitone := Or.inl (by
    intro i j hij
    have hcomp :
        (homOfLE (Fin.zero_le i) : (0 : Fin (k + 1)) ⟶ i) ≫
          homOfLE hij = homOfLE (Fin.zero_le j) := by
      subsingleton
    have hlen := congrArg (fun f ↦ letterLength (F.map f)) hcomp
    dsimp only at hlen
    rw [F.map_comp, letterLength_comp] at hlen
    change letterLength (F.map (homOfLE (Fin.zero_le i))) ≤
      letterLength (F.map (homOfLE (Fin.zero_le j)))
    omega)

/-- The prefix-length parameter preserves both endpoints. -/
theorem prefixParameter_zero {k m : ℕ}
    (F : Fin (k + 1) ⥤ FreeDaggerSimplex m) :
    (prefixParameter F).toFun 0 = 0 := by
  apply Fin.ext
  change letterLength (F.map (homOfLE (Fin.zero_le (0 : Fin (k + 1))))) = 0
  simpa only [homOfLE_refl, F.map_id] using letterLength_id (F.obj 0)

theorem prefixParameter_last {k m : ℕ}
    (F : Fin (k + 1) ⥤ FreeDaggerSimplex m) :
    (prefixParameter F).toFun (Fin.last k) = Fin.last (letterLength (fullPath F)) := by
  apply Fin.ext
  rfl

/-- Prefix lengths are monotone in the chain index. -/
theorem prefixParameter_monotone {k m : ℕ}
    (F : Fin (k + 1) ⥤ FreeDaggerSimplex m) :
    Monotone (prefixParameter F).toFun := by
  intro i j hij
  have hcomp :
      (homOfLE (Fin.zero_le i) : (0 : Fin (k + 1)) ⟶ i) ≫
        homOfLE hij = homOfLE (Fin.zero_le j) := by
    subsingleton
  have hlen := congrArg (fun f ↦ letterLength (F.map f)) hcomp
  dsimp only at hlen
  rw [F.map_comp, letterLength_comp] at hlen
  change letterLength (F.map (homOfLE (Fin.zero_le i))) ≤
    letterLength (F.map (homOfLE (Fin.zero_le j)))
  omega

/-- The canonical parameter is monotone and interior. -/
theorem prefixParameter_interior {k m : ℕ}
    (F : Fin (k + 1) ⥤ FreeDaggerSimplex m) :
    CharacteristicInterior.Interior (prefixParameter F) := by
  left
  exact ⟨prefixParameter_monotone F, prefixParameter_zero F,
    prefixParameter_last F⟩

/-- The full path has exactly the total letter length of the chain. -/
theorem totalLength_eq_fullPath {k m : ℕ}
    (F : Fin (k + 1) ⥤ FreeDaggerSimplex m) :
    totalLength k m F = letterLength (fullPath F) :=
  totalLength_eq_composite m k F

/-- Every native chain is the pullback of the letter chain of its actual
unreduced whole path along its canonical monotone interior parameter. -/
theorem extensionMap_prefixParameter {k m : ℕ}
    (F : Fin (k + 1) ⥤ FreeDaggerSimplex m) :
    (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
      (FreeDaggerSimplex m)).extensionMap
        (prefixParameter F) (letterChain (fullPath F)) = F := by
  let p := fullPath F
  let φ := prefixParameter F
  let G : Fin (k + 1) ⥤ FreeDaggerSimplex m :=
    (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
      (FreeDaggerSimplex m)).extensionMap φ (letterChain p)
  have hφ : Monotone φ.toFun := prefixParameter_monotone F
  have hzero : φ.toFun 0 = 0 := prefixParameter_zero F
  have hlast : φ.toFun (Fin.last k) = Fin.last (letterLength p) :=
    prefixParameter_last F
  have hwhole : compositeArrow F = compositeArrow G := by
    calc
      compositeArrow F = Arrow.mk p := rfl
      _ = compositeArrow (letterChain p) := (compositeArrow_letterChain p).symm
      _ = compositeArrow G :=
        (compositeArrow_monotone_endpoints (letterChain p) φ hφ hzero hlast).symm
  have hlen (i : Fin (k + 1)) :
      letterLength (F.map (homOfLE (Fin.zero_le i))) =
        letterLength (G.map (homOfLE (Fin.zero_le i))) := by
    rw [pullback_prefixLength (letterChain p) (letterChain_adjacent_length p)
      φ hφ i]
    simp only [hzero, Fin.val_zero, Nat.sub_zero]
    rfl
  exact (chain_eq_of_compositeArrow_eq_and_prefixLengths F G hwhole hlen).symm

/-- The actual characteristic map classifies every native chain. -/
theorem characteristic_covers_chain {k m : ℕ}
    (F : Fin (k + 1) ⥤ FreeDaggerSimplex m) :
    (characteristic (fullPath F)).app
      (op (⟨k⟩ : ReverseSimplex)) (prefixParameter F) = F := by
  rw [characteristic_app]
  exact extensionMap_prefixParameter F

end

end DaggerModels.PartII.ChainPathCoverage
