import DaggerModelsPartII.FreeDaggerPathChains

/-!
# Recovering a monotone characteristic-map parameter from lengths

For a chain of individual letters, every interval has the length of its
index interval. A monotone pullback that preserves the initial vertex
therefore determines its indexing map from its prefix lengths.
-/

set_option autoImplicit false

open CategoryTheory Opposite DaggerModels
open DaggerModelsPartII.DaggerSimplexIndex

namespace DaggerModels.PartII.CharacteristicLengthRecovery

open DaggerNerveLengthFiltration FreeDaggerPathChains

noncomputable section

/-- The prefix ending at index i in a chain of letters has exactly i letters. -/
theorem prefixLength_eq_index {n m : ℕ}
    (F : Fin (n + 1) ⥤ FreeDaggerSimplex m)
    (hF : ∀ i : Fin n,
      letterLength (F.map (homOfLE (Fin.castSucc_le_succ i))) = 1)
    (i : Fin (n + 1)) :
    letterLength (F.map (homOfLE (Fin.zero_le i))) = i.val := by
  induction i using Fin.induction with
  | zero =>
    change letterLength (F.map (𝟙 (0 : Fin (n + 1)))) = 0
    rw [F.map_id, letterLength_id]
  | succ i ih =>
    have hcomp :
        (homOfLE (Fin.zero_le i.castSucc) : (0 : Fin (n + 1)) ⟶ i.castSucc) ≫
          homOfLE (Fin.castSucc_le_succ i) = homOfLE (Fin.zero_le i.succ) := by
      subsingleton
    rw [← hcomp, F.map_comp, letterLength_comp, hF i, ih]
    rfl

/-- The length of any interval in a letter chain is the difference of indices. -/
theorem intervalLength_eq_index_sub {n m : ℕ}
    (F : Fin (n + 1) ⥤ FreeDaggerSimplex m)
    (hF : ∀ i : Fin n,
      letterLength (F.map (homOfLE (Fin.castSucc_le_succ i))) = 1)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    letterLength (F.map (homOfLE hij)) = j.val - i.val := by
  have hcomp :
      (homOfLE (Fin.zero_le i) : (0 : Fin (n + 1)) ⟶ i) ≫
        homOfLE hij = homOfLE (Fin.zero_le j) := by
    subsingleton
  have hlen := congrArg (fun f ↦ letterLength (F.map f)) hcomp
  dsimp only at hlen
  rw [F.map_comp, letterLength_comp,
    prefixLength_eq_index F hF i, prefixLength_eq_index F hF j] at hlen
  omega

/-- Prefix lengths of a monotone pullback recover its displacement from
the initial image vertex. -/
theorem pullback_prefixLength {n m : ℕ}
    (F : Fin (n + 1) ⥤ FreeDaggerSimplex m)
    (hF : ∀ i : Fin n,
      letterLength (F.map (homOfLE (Fin.castSucc_le_succ i))) = 1)
    {k : ReverseSimplex} (φ : k ⟶ (⟨n⟩ : ReverseSimplex))
    (hφ : Monotone φ.toFun) (i : Fin (k.len + 1)) :
    letterLength
      (((DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
        (FreeDaggerSimplex m)).extensionMap φ F).map
          (homOfLE (Fin.zero_le i))) = (φ.toFun i).val - (φ.toFun 0).val := by
  rw [DaggerSSet.extensionMap_monotone _ φ hφ]
  exact intervalLength_eq_index_sub F hF (hφ (Fin.zero_le i))

/-- For two monotone parameters starting at zero, equal pullback chains
force the actual reversal-simplex maps to be equal. -/
theorem monotone_parameter_injective {n m : ℕ}
    (F : Fin (n + 1) ⥤ FreeDaggerSimplex m)
    (hF : ∀ i : Fin n,
      letterLength (F.map (homOfLE (Fin.castSucc_le_succ i))) = 1)
    {k : ReverseSimplex} (φ ψ : k ⟶ (⟨n⟩ : ReverseSimplex))
    (hφ : Monotone φ.toFun) (hψ : Monotone ψ.toFun)
    (hφzero : φ.toFun 0 = 0) (hψzero : ψ.toFun 0 = 0)
    (heq : (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
        (FreeDaggerSimplex m)).extensionMap φ F =
      (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
        (FreeDaggerSimplex m)).extensionMap ψ F) : φ = ψ := by
  apply ReverseSimplex.Hom.ext
  intro i
  apply Fin.ext
  have hprefix := congrArg
    (fun G : Fin (k.len + 1) ⥤ FreeDaggerSimplex m ↦
      letterLength (G.map (homOfLE (Fin.zero_le i)))) heq
  dsimp only at hprefix
  rw [pullback_prefixLength F hF φ hφ i, pullback_prefixLength F hF ψ hψ i,
    hφzero, hψzero] at hprefix
  simpa using hprefix

/-- In particular, a path's characteristic map is injective on its
monotone parameters that start at the initial vertex. -/
theorem characteristic_monotone_injective {m : ℕ} {a b : FreeDaggerSimplex m}
    (p : a ⟶ b) {k : ReverseSimplex}
    (φ ψ : k ⟶ (⟨letterLength p⟩ : ReverseSimplex))
    (hφ : Monotone φ.toFun) (hψ : Monotone ψ.toFun)
    (hφzero : φ.toFun 0 = 0) (hψzero : ψ.toFun 0 = 0)
    (heq : (characteristic p).app (op k) φ =
      (characteristic p).app (op k) ψ) : φ = ψ := by
  rw [characteristic_app, characteristic_app] at heq
  exact monotone_parameter_injective (letterChain p)
    (letterChain_adjacent_length p) φ ψ hφ hψ hφzero hψzero heq

/-- For two antitone parameters ending at zero, reversing the source
reduces recovery to the monotone case. -/
theorem antitone_parameter_injective {n m : ℕ}
    (F : Fin (n + 1) ⥤ FreeDaggerSimplex m)
    (hF : ∀ i : Fin n,
      letterLength (F.map (homOfLE (Fin.castSucc_le_succ i))) = 1)
    {k : ReverseSimplex} (φ ψ : k ⟶ (⟨n⟩ : ReverseSimplex))
    (hφ : Antitone φ.toFun) (hψ : Antitone ψ.toFun)
    (hφlast : φ.toFun (Fin.last k.len) = 0)
    (hψlast : ψ.toFun (Fin.last k.len) = 0)
    (heq : (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
        (FreeDaggerSimplex m)).extensionMap φ F =
      (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
        (FreeDaggerSimplex m)).extensionMap ψ F) : φ = ψ := by
  let α := ReverseSimplex.reversal k ≫ φ
  let β := ReverseSimplex.reversal k ≫ ψ
  have hα : Monotone α.toFun := by
    intro i j hij
    exact hφ (Fin.rev_le_rev.mpr hij)
  have hβ : Monotone β.toFun := by
    intro i j hij
    exact hψ (Fin.rev_le_rev.mpr hij)
  have hαzero : α.toFun 0 = 0 := by
    change φ.toFun (Fin.rev 0) = 0
    simpa using hφlast
  have hβzero : β.toFun 0 = 0 := by
    change ψ.toFun (Fin.rev 0) = 0
    simpa using hψlast
  let X := DaggerNativeOrdinaryDaggerNerveLift.daggerNerve (FreeDaggerSimplex m)
  have heq' : X.extensionMap α F = X.extensionMap β F := by
    change X.extensionMap (ReverseSimplex.reversal k ≫ φ) F =
      X.extensionMap (ReverseSimplex.reversal k ≫ ψ) F
    rw [X.extensionMap_comp, X.extensionMap_comp, heq]
  have hab := monotone_parameter_injective F hF α β hα hβ hαzero hβzero heq'
  have h := congrArg (fun f ↦ ReverseSimplex.reversal k ≫ f) hab
  dsimp only [α, β] at h
  simpa only [← Category.assoc, ReverseSimplex.reversal_comp_reversal,
    Category.id_comp] using h

/-- A path's characteristic map is injective on antitone parameters
ending at the initial vertex. -/
theorem characteristic_antitone_injective {m : ℕ} {a b : FreeDaggerSimplex m}
    (p : a ⟶ b) {k : ReverseSimplex}
    (φ ψ : k ⟶ (⟨letterLength p⟩ : ReverseSimplex))
    (hφ : Antitone φ.toFun) (hψ : Antitone ψ.toFun)
    (hφlast : φ.toFun (Fin.last k.len) = 0)
    (hψlast : ψ.toFun (Fin.last k.len) = 0)
    (heq : (characteristic p).app (op k) φ =
      (characteristic p).app (op k) ψ) : φ = ψ := by
  rw [characteristic_app, characteristic_app] at heq
  exact antitone_parameter_injective (letterChain p)
    (letterChain_adjacent_length p) φ ψ hφ hψ hφlast hψlast heq

end

end DaggerModels.PartII.CharacteristicLengthRecovery
