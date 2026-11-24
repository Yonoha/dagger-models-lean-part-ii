import DaggerModelsPartII.DaggerSimplexNerveNaturality
import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# Total letter length in the native free dagger simplex nerve

The length of a chain is the sum of the lengths of its adjacent path arrows.
Each path is a word in the doubled line quiver, with no cancellation imposed.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerModelsPartII.DaggerSimplexIndex
open DaggerModels.PartII.DaggerSimplexPartIIndex
open DaggerModels.PartII.DaggerSimplexNerveRepresentable
open DaggerModels.PartII.DaggerSimplexNerveNaturality

namespace DaggerModels.PartII.DaggerNerveLengthFiltration

noncomputable section

/-- The letter length of an arrow of a free dagger simplex. -/
def letterLength {m : ℕ} {a b : FreeDaggerSimplex m} (p : a ⟶ b) : ℕ :=
  Quiver.Path.length p

@[simp] theorem letterLength_id {m : ℕ} (a : FreeDaggerSimplex m) :
    letterLength (𝟙 a) = 0 := rfl

theorem letterLength_comp {m : ℕ} {a b c : FreeDaggerSimplex m}
    (p : a ⟶ b) (q : b ⟶ c) :
    letterLength (p ≫ q) = letterLength p + letterLength q :=
  Quiver.Path.length_comp p q

theorem pathLength_reverse {V : Type*} [Quiver V] [Quiver.HasReverse V]
    {a b : V} (p : Quiver.Path a b) : p.reverse.length = p.length := by
  induction p with
  | nil => rfl
  | cons q e ih =>
      rw [Quiver.Path.reverse, Quiver.Path.length_comp, Quiver.Path.length_toPath,
        Quiver.Path.length_cons, ih]
      omega

theorem freeChain_map_heq {k m : ℕ}
    (F : Fin (k + 1) ⥤ FreeDaggerSimplex m)
    {i j i' j' : Fin (k + 1)} (hi : i = i') (hj : j = j')
    (f : i ⟶ j) (g : i' ⟶ j') : F.map f ≍ F.map g := by
  cases hi
  cases hj
  exact heq_of_eq (congrArg F.map (Subsingleton.elim f g))

theorem letterLength_dagger {m : ℕ} {a b : FreeDaggerSimplex m}
    (p : a ⟶ b) : letterLength (dagger p) = letterLength p := by
  change (Quiver.Path.reverse p).length = p.length
  exact pathLength_reverse p

/-- The native nerve chain has one length contribution for each adjacent arrow. -/
def totalLength (k m : ℕ) (F : Fin (k + 1) ⥤ FreeDaggerSimplex m) : ℕ :=
  ∑ i : Fin k, letterLength (F.map (homOfLE (Fin.castSucc_le_succ i)))

/-- The initial segment of a chain, omitting its final vertex. -/
def initialChain {k m : ℕ} (F : Fin (k + 2) ⥤ FreeDaggerSimplex m) :
    Fin (k + 1) ⥤ FreeDaggerSimplex m where
  obj i := F.obj i.castSucc
  map {i j} h := F.map (homOfLE (Fin.castSucc_le_castSucc_iff.mpr (leOfHom h)))
  map_id i := by
    change F.map (𝟙 i.castSucc) = 𝟙 (F.obj i.castSucc)
    exact F.map_id _
  map_comp f g := by
    rw [← F.map_comp]
    congr 1

/-- The adjacent-arrow sum is the path length of the composite from the
first to the last vertex. -/
theorem totalLength_eq_composite (m : ℕ) : ∀ (k : ℕ)
    (F : Fin (k + 1) ⥤ FreeDaggerSimplex m),
    totalLength k m F =
      letterLength (F.map (homOfLE (Fin.zero_le (Fin.last k)))) := by
  intro k
  induction k with
  | zero =>
      intro F
      simp [totalLength, letterLength]
      rfl
  | succ k ih =>
      intro F
      rw [totalLength, Fin.sum_univ_castSucc]
      have hinit :
          (∑ i : Fin k,
            letterLength (F.map (homOfLE (Fin.castSucc_le_succ i.castSucc)))) =
          totalLength k m (initialChain F) := by
        rfl
      rw [hinit, ih]
      have hcomp :
          (homOfLE (Fin.zero_le (Fin.last k).castSucc) :
            (0 : Fin (k + 2)) ⟶ (Fin.last k).castSucc) ≫
              homOfLE (Fin.castSucc_le_succ (Fin.last k)) =
            homOfLE (Fin.zero_le (Fin.last (k + 1))) := by
        subsingleton
      rw [← hcomp, F.map_comp, letterLength_comp]
      rfl

/-- A subinterval arrow occupies a contiguous subword of the whole chain. -/
theorem intervalLength_le_total {k m : ℕ}
    (F : Fin (k + 1) ⥤ FreeDaggerSimplex m)
    {i j : Fin (k + 1)} (hij : i ≤ j) :
    letterLength (F.map (homOfLE hij)) ≤ totalLength k m F := by
  rw [totalLength_eq_composite]
  have hfactor :
      (homOfLE (Fin.zero_le i) : (0 : Fin (k + 1)) ⟶ i) ≫
          homOfLE hij ≫ homOfLE (Fin.le_last j) =
        homOfLE (Fin.zero_le (Fin.last k)) := by
    subsingleton
  rw [← hfactor, F.map_comp, F.map_comp, letterLength_comp, letterLength_comp]
  omega

theorem intervalLength_eq_total_of_endpoints {k m : ℕ}
    (F : Fin (k + 1) ⥤ FreeDaggerSimplex m)
    {i j : Fin (k + 1)} (hij : i ≤ j)
    (hi : i = 0) (hj : j = Fin.last k) :
    letterLength (F.map (homOfLE hij)) = totalLength k m F := by
  cases hi
  cases hj
  exact (totalLength_eq_composite m k F).symm

/-- Ordinary monotone simplicial operators cannot increase total letter length. -/
theorem totalLength_extensionMap_monotone {l k : ReverseSimplex} (m : ℕ)
    (α : l ⟶ k) (hα : Monotone α.toFun)
    (F : Fin (k.len + 1) ⥤ FreeDaggerSimplex m) :
    totalLength l.len m
        ((DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
          (FreeDaggerSimplex m)).extensionMap α F) ≤ totalLength k.len m F := by
  let X := DaggerNativeOrdinaryDaggerNerveLift.daggerNerve (FreeDaggerSimplex m)
  have hends : α.toFun 0 ≤ α.toFun (Fin.last l.len) :=
    hα (Fin.zero_le (Fin.last l.len))
  calc
    totalLength l.len m (X.extensionMap α F) =
        letterLength ((X.extensionMap α F).map
          (homOfLE (Fin.zero_le (Fin.last l.len)))) :=
      totalLength_eq_composite m l.len _
    _ = letterLength (F.map (homOfLE hends)) := by
      rw [X.extensionMap_monotone α hα]
      rfl
    _ ≤ totalLength k.len m F := intervalLength_le_total F hends

/-- A monotone operator preserving both endpoints preserves total length. -/
theorem totalLength_extensionMap_monotone_endpoints {l k : ReverseSimplex} (m : ℕ)
    (α : l ⟶ k) (hα : Monotone α.toFun)
    (hzero : α.toFun 0 = 0)
    (hlast : α.toFun (Fin.last l.len) = Fin.last k.len)
    (F : Fin (k.len + 1) ⥤ FreeDaggerSimplex m) :
    totalLength l.len m
        ((DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
          (FreeDaggerSimplex m)).extensionMap α F) = totalLength k.len m F := by
  let X := DaggerNativeOrdinaryDaggerNerveLift.daggerNerve (FreeDaggerSimplex m)
  have hends : α.toFun 0 ≤ α.toFun (Fin.last l.len) :=
    hα (Fin.zero_le (Fin.last l.len))
  calc
    totalLength l.len m (X.extensionMap α F) =
        letterLength ((X.extensionMap α F).map
          (homOfLE (Fin.zero_le (Fin.last l.len)))) :=
      totalLength_eq_composite m l.len _
    _ = letterLength (F.map (homOfLE hends)) := by
      rw [X.extensionMap_monotone α hα]
      rfl
    _ = totalLength k.len m F :=
      intervalLength_eq_total_of_endpoints F hends hzero hlast

/-- In particular, monotone surjections, including simplicial degeneracies,
preserve total length. -/
theorem totalLength_extensionMap_surjective {l k : ReverseSimplex} (m : ℕ)
    (α : l ⟶ k) (hα : Monotone α.toFun) (hsurj : Function.Surjective α.toFun)
    (F : Fin (k.len + 1) ⥤ FreeDaggerSimplex m) :
    totalLength l.len m
        ((DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
          (FreeDaggerSimplex m)).extensionMap α F) = totalLength k.len m F := by
  obtain ⟨i, hi⟩ := hsurj 0
  have hzero : α.toFun 0 = 0 := by
    apply le_antisymm
    · rw [← hi]
      exact hα (Fin.zero_le i)
    · exact Fin.zero_le _
  obtain ⟨j, hj⟩ := hsurj (Fin.last k.len)
  have hlast : α.toFun (Fin.last l.len) = Fin.last k.len := by
    apply le_antisymm
    · exact Fin.le_last _
    · rw [← hj]
      exact hα (Fin.le_last j)
  exact totalLength_extensionMap_monotone_endpoints m α hα hzero hlast F

/-- Reversal reverses the composite word and daggers every letter, preserving
its total length. -/
theorem totalLength_extensionMap_reversal (k : ReverseSimplex) (m : ℕ)
    (F : Fin (k.len + 1) ⥤ FreeDaggerSimplex m) :
    totalLength k.len m
        ((DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
          (FreeDaggerSimplex m)).extensionMap (ReverseSimplex.reversal k) F) =
      totalLength k.len m F := by
  let X := DaggerNativeOrdinaryDaggerNerveLift.daggerNerve (FreeDaggerSimplex m)
  have ha : Antitone (ReverseSimplex.reversal k).toFun := by
    intro i j h
    simpa only [ReverseSimplex.reversal_apply, Fin.rev_le_rev] using h
  have hid : ReverseSimplex.antitoneHom (ReverseSimplex.reversal k) ha = 𝟙 ⦋k.len⦌ := by
    ext i
    simp [ReverseSimplex.antitoneHom]
  calc
    totalLength k.len m (X.extensionMap (ReverseSimplex.reversal k) F) =
        letterLength ((X.extensionMap (ReverseSimplex.reversal k) F).map
          (homOfLE (Fin.zero_le (Fin.last k.len)))) :=
      totalLength_eq_composite m k.len _
    _ = letterLength (dagger (F.map
          (homOfLE (Fin.zero_le (Fin.last k.len))))) := by
      rw [X.extensionMap_antitone (ReverseSimplex.reversal k) ha, hid,
        op_id, X.toSSet.map_id]
      change letterLength ((SSet.opObjEquiv
        ((DaggerNativeOrdinaryDaggerNerve.reversal (FreeDaggerSimplex m)).app
          (op ⦋k.len⦌) F)).map (homOfLE (Fin.zero_le (Fin.last k.len)))) = _
      rw [DaggerNativeOrdinaryDaggerNerve.reversal_map]
      simp [DaggerOriginalNerveOppositeMap.reverseDiagram,
        ComposableArrows.opEquivalence, Fin.revOrderIso]
      congr 1
      · simpa using DaggerNativeOrdinaryDaggerNerve.reversal_obj
          (FreeDaggerSimplex m) ⦋k.len⦌ F (Fin.last k.len)
      · congr 1
        · simp
        · apply freeChain_map_heq F
          · simp
          · simp
    _ = letterLength (F.map (homOfLE (Fin.zero_le (Fin.last k.len)))) :=
      letterLength_dagger _
    _ = totalLength k.len m F := (totalLength_eq_composite m k.len F).symm

/-- Every reversal-simplex operator has nonincreasing total length. -/
theorem totalLength_extensionMap {l k : ReverseSimplex} (m : ℕ)
    (α : l ⟶ k) (F : Fin (k.len + 1) ⥤ FreeDaggerSimplex m) :
    totalLength l.len m
        ((DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
          (FreeDaggerSimplex m)).extensionMap α F) ≤ totalLength k.len m F := by
  rcases α.monotone_or_antitone with hα | hα
  · exact totalLength_extensionMap_monotone m α hα F
  · let β : l ⟶ k := ReverseSimplex.inclusion.map
      (ReverseSimplex.antitoneHom α hα)
    have hβ : Monotone β.toFun :=
      (ReverseSimplex.antitoneHom α hα).toOrderHom.monotone
    have hfac : β ≫ ReverseSimplex.reversal k = α :=
      ReverseSimplex.antitone_factorization α hα
    let X := DaggerNativeOrdinaryDaggerNerveLift.daggerNerve (FreeDaggerSimplex m)
    calc
      totalLength l.len m (X.extensionMap α F) =
          totalLength l.len m
            (X.extensionMap β (X.extensionMap (ReverseSimplex.reversal k) F)) := by
        rw [← X.extensionMap_comp, hfac]
      _ ≤ totalLength k.len m (X.extensionMap (ReverseSimplex.reversal k) F) :=
        totalLength_extensionMap_monotone m β hβ _
      _ = totalLength k.len m F := totalLength_extensionMap_reversal k m F

/-- Chains of total letter length at most `ell` form a subpresheaf of the
native dagger nerve on the reversal-simplex category. -/
def lengthFiltration (m ell : ℕ) :
    Subfunctor ((DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
      (FreeDaggerSimplex m)).extension) where
  obj k := {F | totalLength k.unop.len m F ≤ ell}
  map α F hF := (totalLength_extensionMap m α.unop F).trans hF

theorem lengthFiltration_mono (m : ℕ) : Monotone (lengthFiltration m) := by
  intro ell ell' h k F hF
  exact hF.trans h

theorem lengthFiltration_exhaustive (m : ℕ) :
    (⨆ ell, lengthFiltration m ell) = ⊤ := by
  apply Subfunctor.ext
  funext k
  ext F
  constructor
  · intro _
    trivial
  · intro _
    simp only [Subfunctor.iSup_obj, Set.mem_iUnion]
    refine ⟨totalLength k.unop.len m F, ?_⟩
    change totalLength k.unop.len m F ≤ totalLength k.unop.len m F
    exact le_rfl

/-- Length of a chain corresponding to an actual enriched dagger functor. -/
def actualHomLength (k m : ℕ)
    (F : (⟨k⟩ : ActualDaggerSimplex) ⟶ ⟨m⟩) : ℕ :=
  totalLength k m (actualHomChainEquiv k m F)

/-- Source precomposition by an actual reversal map is length nonincreasing
under the all-functor chain equivalence. -/
theorem actualHomLength_precomp {l k : ReverseSimplex} (m : ℕ)
    (α : l ⟶ k) (F : (⟨k.len⟩ : ActualDaggerSimplex) ⟶ ⟨m⟩) :
    actualHomLength l.len m (actualU.map α ≫ F) ≤ actualHomLength k.len m F := by
  change totalLength l.len m
      (actualHomNativeNerveEquiv l.len m (actualU.map α ≫ F)) ≤
    totalLength k.len m (actualHomNativeNerveEquiv k.len m F)
  rw [actualHomNativeNerveEquiv_precomp]
  exact totalLength_extensionMap m α _

end

end DaggerModels.PartII.DaggerNerveLengthFiltration
