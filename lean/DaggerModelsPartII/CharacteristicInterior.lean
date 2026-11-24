import DaggerModelsPartII.CharacteristicLengthRecovery
import DaggerModelsPartII.CharacteristicOuterBoundary
import DaggerModelsPartII.ReversalOuterFaceAction

/-!
# Interior parameters of a letter-chain characteristic map

An interior reversal-simplex map meets both endpoint vertices, in either
orientation. This is exactly the complement of the literal outer-face union,
and exactly the locus where the characteristic pullback retains full length.
-/

set_option autoImplicit false

open CategoryTheory Opposite DaggerModels
open DaggerModelsPartII.DaggerSimplexIndex

namespace DaggerModels.PartII.CharacteristicInterior

open DaggerNerveLengthFiltration FreeDaggerPathChains
open CharacteristicLengthRecovery ReversalOuterFaceSubobject
open ReversalRepresentableFixedPoints ReversalOuterFaceAction

noncomputable section

/-- The two endpoint and orientation cases of an interior parameter. -/
def Interior {k : ReverseSimplex} {n : ℕ}
    (φ : k ⟶ (⟨n⟩ : ReverseSimplex)) : Prop :=
  (Monotone φ.toFun ∧ φ.toFun 0 = 0 ∧
    φ.toFun (Fin.last k.len) = Fin.last n) ∨
  (Antitone φ.toFun ∧ φ.toFun 0 = Fin.last n ∧
    φ.toFun (Fin.last k.len) = 0)

private theorem outerFace_iff_omits {k : ReverseSimplex} {n : ℕ}
    (hn : 1 ≤ n) (φ : k ⟶ (⟨n⟩ : ReverseSimplex)) :
    φ ∈ (outerFaceSubpresheafAt n hn).obj (op k) ↔
      (∀ i, φ.toFun i ≠ 0) ∨ (∀ i, φ.toFun i ≠ Fin.last n) := by
  cases n with
  | zero => omega
  | succ t =>
    change φ ∈ (outerFaceSubpresheaf t).obj (op k) ↔ _
    constructor
    · intro h
      rcases h with ⟨g, hg⟩ | ⟨g, hg⟩
      · left
        intro i hi
        change g ≫ firstOuterCoface t = φ at hg
        have he := congrArg (fun f : k ⟶ (⟨t + 1⟩ : ReverseSimplex) ↦
          (f.toFun i).val) hg
        change (g.toFun i).val + 1 = (φ.toFun i).val at he
        have hv := congrArg Fin.val hi
        change (φ.toFun i).val = 0 at hv
        omega
      · right
        intro i hi
        change g ≫ lastOuterCoface t = φ at hg
        have he := congrArg (fun f : k ⟶ (⟨t + 1⟩ : ReverseSimplex) ↦
          (f.toFun i).val) hg
        change (g.toFun i).val = (φ.toFun i).val at he
        have hv := congrArg Fin.val hi
        have hglt := (g.toFun i).isLt
        change (g.toFun i).val < t + 1 at hglt
        change (φ.toFun i).val = t + 1 at hv
        omega
    · rintro (hzero | hlast)
      · have hflip : ∀ i : Fin (k.len + 1),
            ((flip φ).toFun i).val < t + 1 := by
          intro i
          have hz : (φ.toFun i).val ≠ 0 := by
            intro he
            exact hzero i (Fin.ext he)
          have hlt := (φ.toFun i).isLt
          rw [flip_apply, Fin.val_rev]
          change t + 2 - ((φ.toFun i).val + 1) < t + 1
          omega
        have hmem := mem_outerFaceSubpresheaf_of_omits_last (flip φ) hflip
        have hmem' := flip_mem_outerFaceSubpresheaf t (flip φ) hmem
        simpa only [flip_flip] using hmem'
      · apply mem_outerFaceSubpresheaf_of_omits_last
        intro i
        have hne : (φ.toFun i).val ≠ t + 1 := by
          intro he
          exact hlast i (Fin.ext he)
        have hlt := (φ.toFun i).isLt
        change (φ.toFun i).val < t + 2 at hlt
        omega

private theorem not_interior_iff_omits {k : ReverseSimplex} {n : ℕ}
    (φ : k ⟶ (⟨n⟩ : ReverseSimplex)) :
    ¬ Interior φ ↔
      (∀ i, φ.toFun i ≠ 0) ∨ (∀ i, φ.toFun i ≠ Fin.last n) := by
  constructor
  · intro h
    by_cases hz : ∀ i, φ.toFun i ≠ 0
    · exact Or.inl hz
    by_cases hl : ∀ i, φ.toFun i ≠ Fin.last n
    · exact Or.inr hl
    push_neg at hz hl
    obtain ⟨i, hi⟩ := hz
    obtain ⟨j, hj⟩ := hl
    exfalso
    rcases φ.monotone_or_antitone with hm | ha
    · apply h (Or.inl ⟨hm, ?_, ?_⟩)
      · exact le_antisymm (hi ▸ hm (Fin.zero_le i)) (Fin.zero_le _)
      · exact le_antisymm (Fin.le_last _) (hj ▸ hm (Fin.le_last j))
    · apply h (Or.inr ⟨ha, ?_, ?_⟩)
      · exact le_antisymm (Fin.le_last _) (hj ▸ ha (Fin.zero_le j))
      · exact le_antisymm (hi ▸ ha (Fin.le_last i)) (Fin.zero_le _)
  · rintro (hz | hl) h
    · rcases h with ⟨_, h0, _⟩ | ⟨_, _, h0⟩
      · exact hz 0 h0
      · exact hz (Fin.last k.len) h0
    · rcases h with ⟨_, _, hlast⟩ | ⟨_, hlast, _⟩
      · exact hl (Fin.last k.len) hlast
      · exact hl 0 hlast

/-- The literal outer-face union consists exactly of non-interior maps. -/
theorem mem_outerFace_iff_not_interior {k : ReverseSimplex} {n : ℕ}
    (hn : 1 ≤ n) (φ : k ⟶ (⟨n⟩ : ReverseSimplex)) :
    φ ∈ (outerFaceSubpresheafAt n hn).obj (op k) ↔ ¬ Interior φ := by
  rw [outerFace_iff_omits hn φ, not_interior_iff_omits]

/-- A characteristic pullback retains the path's entire length exactly for
the two interior endpoint configurations. -/
theorem characteristic_totalLength_eq_iff_interior {m : ℕ}
    {a b : FreeDaggerSimplex m} (p : a ⟶ b)
    (hp : 1 ≤ letterLength p) {k : ReverseSimplex}
    (φ : k ⟶ (⟨letterLength p⟩ : ReverseSimplex)) :
    totalLength k.len m
      ((DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
        (FreeDaggerSimplex m)).extensionMap φ (letterChain p)) =
      letterLength p ↔ Interior φ := by
  let X := DaggerNativeOrdinaryDaggerNerveLift.daggerNerve (FreeDaggerSimplex m)
  constructor
  · intro heq
    by_contra hnot
    have hmem := (mem_outerFace_iff_not_interior hp φ).mpr hnot
    have hbound := CharacteristicOuterBoundary.totalLength_outerFaceAt hp
      (letterChain p) (letterChain_adjacent_length p) φ hmem
    omega
  · intro h
    rcases h with ⟨hmono, hzero, hlast⟩ | ⟨hanti, hfirst, hfinal⟩
    · exact (totalLength_extensionMap_monotone_endpoints m φ hmono hzero hlast
        (letterChain p)).trans (totalLength_letterChain p)
    · let ψ : k ⟶ (⟨letterLength p⟩ : ReverseSimplex) :=
        ReverseSimplex.reversal k ≫ φ
      have hψmono : Monotone ψ.toFun := by
        intro i j hij
        exact hanti (Fin.rev_le_rev.mpr hij)
      have hψzero : ψ.toFun 0 = 0 := by
        change φ.toFun (Fin.rev 0) = 0
        simpa using hfinal
      have hψlast : ψ.toFun (Fin.last k.len) = Fin.last (letterLength p) := by
        change φ.toFun (Fin.rev (Fin.last k.len)) = Fin.last (letterLength p)
        simpa using hfirst
      have hfull := (totalLength_extensionMap_monotone_endpoints m ψ
        hψmono hψzero hψlast (letterChain p)).trans (totalLength_letterChain p)
      have hreverse :
          totalLength k.len m (X.extensionMap ψ (letterChain p)) =
            totalLength k.len m (X.extensionMap φ (letterChain p)) := by
        change totalLength k.len m
          (X.extensionMap (ReverseSimplex.reversal k ≫ φ) (letterChain p)) = _
        rw [X.extensionMap_comp]
        exact totalLength_extensionMap_reversal k m (X.extensionMap φ (letterChain p))
      exact hreverse.symm.trans hfull

end

end DaggerModels.PartII.CharacteristicInterior
