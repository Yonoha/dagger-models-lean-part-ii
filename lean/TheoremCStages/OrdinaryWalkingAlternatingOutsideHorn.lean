import OrdinaryWalkingAlternatingAttachment

/-!
# Simplex operators outside the zero outer horn

An operator outside `Λ[k+2,0]` visits every positive vertex. It either also
visits zero, hence is epi onto the whole ordinal, or factors uniquely through
the missing zero face with an epi residual operator. This is the operator
factorization needed to reduce the reverse preimage and off-horn uniqueness
to the two nondegenerate alternating words.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.OrdinaryWalkingAlternatingOutsideHorn

noncomputable section

/-- The complement of the zero outer horn is characterized by visiting
every positive vertex of the standard simplex. -/
theorem not_mem_horn_iff_positive_range (k m : ℕ)
    (s : (Δ[k + 2] : SSet).obj (op ⦋m⦌)) :
    s ∉ (SSet.horn (k + 2) (0 : Fin (k + 3))).obj (op ⦋m⦌) ↔
      ∀ i : Fin (k + 3), 0 < i →
        i ∈ Set.range (SSet.stdSimplex.asOrderHom s) := by
  change (¬ Set.range (SSet.stdSimplex.asOrderHom s) ∪
      {(0 : Fin (k + 3))} ≠ Set.univ) ↔ _
  rw [not_not]
  constructor
  · intro h i hi
    have hmem := (Set.eq_univ_iff_forall.mp h) i
    rcases hmem with hmem | hzero
    · exact hmem
    · have : i = 0 := by simpa only [Set.mem_singleton_iff] using hzero
      exact (ne_of_gt hi this).elim
  · intro h
    apply Set.eq_univ_of_forall
    intro i
    by_cases hi : i = 0
    · exact Or.inr (by simpa only [Set.mem_singleton_iff] using hi)
    · exact Or.inl (h i (Fin.pos_iff_ne_zero.mpr hi))

/-- Subtract one from an ordinal map whose image omits vertex zero. -/
private def zeroFaceFactor (k m : ℕ) (α : ⦋m⦌ ⟶ ⦋k + 2⦌)
    (hzero : ∀ j : Fin (m + 1), α.toOrderHom j ≠ 0) :
    ⦋m⦌ ⟶ ⦋k + 1⦌ :=
  SimplexCategory.mkHom
    ⟨fun j ↦ ⟨(α.toOrderHom j).val - 1, by
        have hj := (α.toOrderHom j).isLt
        simp only [SimplexCategory.len_mk] at hj
        have hp : 0 < (α.toOrderHom j).val :=
          Fin.val_pos_iff.mpr (Fin.pos_iff_ne_zero.mpr (hzero j))
        omega⟩,
      by
        intro a b hab
        apply Fin.le_iff_val_le_val.mpr
        have hab' := Fin.le_iff_val_le_val.mp
          (α.toOrderHom.monotone hab)
        dsimp
        omega⟩

private theorem zeroFaceFactor_apply (k m : ℕ)
    (α : ⦋m⦌ ⟶ ⦋k + 2⦌)
    (hzero : ∀ j : Fin (m + 1), α.toOrderHom j ≠ 0)
    (j : Fin (m + 1)) :
    ((zeroFaceFactor k m α hzero).toOrderHom j).val =
      (α.toOrderHom j).val - 1 := rfl

/-- The factorization through the missing zero face is an equality of
actual simplex-category operators. -/
private theorem zeroFaceFactor_comp (k m : ℕ)
    (α : ⦋m⦌ ⟶ ⦋k + 2⦌)
    (hzero : ∀ j : Fin (m + 1), α.toOrderHom j ≠ 0) :
    zeroFaceFactor k m α hzero ≫
      SimplexCategory.δ (0 : Fin (k + 3)) = α := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  apply Fin.ext
  change ((0 : Fin (k + 3)).succAbove
      ((zeroFaceFactor k m α hzero).toOrderHom j)).val =
    (α.toOrderHom j).val
  rw [Fin.succAbove_zero_apply, Fin.val_succ,
    zeroFaceFactor_apply]
  have hp : 0 < (α.toOrderHom j).val :=
    Fin.val_pos_iff.mpr (Fin.pos_iff_ne_zero.mpr (hzero j))
  omega

/-- Every simplex operator outside the horn is either epi onto the whole
simplex or epi onto its missing zero face. The latter branch includes the
actual factorization equation, not an abstract image assertion. -/
theorem outside_horn_epi_or_zero_face (k m : ℕ)
    (s : (Δ[k + 2] : SSet).obj (op ⦋m⦌))
    (hs : s ∉ (SSet.horn (k + 2) (0 : Fin (k + 3))).obj (op ⦋m⦌)) :
    Epi (SSet.stdSimplex.objEquiv s) ∨
      ∃ β : ⦋m⦌ ⟶ ⦋k + 1⦌, Epi β ∧
        β ≫ SimplexCategory.δ (0 : Fin (k + 3)) =
          SSet.stdSimplex.objEquiv s := by
  let α : ⦋m⦌ ⟶ ⦋k + 2⦌ := SSet.stdSimplex.objEquiv s
  have hpos : ∀ i : Fin (k + 3), 0 < i →
      i ∈ Set.range α.toOrderHom := by
    simpa only [α] using (not_mem_horn_iff_positive_range k m s).mp hs
  by_cases hzero : (0 : Fin (k + 3)) ∈ Set.range α.toOrderHom
  · left
    apply (SimplexCategory.epi_iff_surjective).2
    intro i
    by_cases hi : i = 0
    · simpa only [hi] using hzero
    · exact hpos i (Fin.pos_iff_ne_zero.mpr hi)
  · right
    have hz : ∀ j : Fin (m + 1), α.toOrderHom j ≠ 0 := by
      intro j hj
      exact hzero ⟨j, hj⟩
    refine ⟨zeroFaceFactor k m α hz, ?_, zeroFaceFactor_comp k m α hz⟩
    apply (SimplexCategory.epi_iff_surjective).2
    intro i
    have hmem := hpos i.succ (Fin.succ_pos i)
    obtain ⟨j, hj⟩ := hmem
    refine ⟨j, ?_⟩
    apply Fin.ext
    rw [zeroFaceFactor_apply]
    have hj' : (α.toOrderHom j).val = i.val + 1 := by
      simpa only [Fin.val_succ] using congrArg Fin.val hj
    omega

#print axioms not_mem_horn_iff_positive_range
#print axioms outside_horn_epi_or_zero_face

end

end DaggerModels.PartII.OrdinaryWalkingAlternatingOutsideHorn
