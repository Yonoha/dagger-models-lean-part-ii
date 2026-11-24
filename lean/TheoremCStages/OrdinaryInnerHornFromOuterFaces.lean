import NativeHornAsPartialFaceUnion
import NativePartialFaceAttachmentAnodyne
import DaggerModelsPartII.ReversalOuterFaceLocality

/-!
# Inner horns from the two outer faces

For a morphism property stable under cobase change and cancellation of a
known first factor when the second factor is monic, the two-outer-face
inclusions imply every inner-horn inclusion. The induction uses the
original unions of codimension-one faces and their literal attachment
pushout squares.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Simplicial MorphismProperty
open DaggerNativePartialFaceUnionGeometry
open DaggerNativePartialFaceAttachmentAnodyne
open DaggerNativeHornAsPartialFaceUnion

namespace DaggerModels.PartII.OrdinaryInnerHornFromOuterFaces

noncomputable section

universe u

private def outerSet (m : ℕ) : Finset (Fin (m + 3)) :=
  insert 0 {Fin.last (m + 2)}

/-- The finite face union is the already used literal union of both outer faces. -/
theorem outerSet_faceUnion (m : ℕ) :
    faceUnion.{u} (outerSet m) =
      ReversalOuterFaceLocality.ordinaryOuterFaces.{u} m := by
  simp only [outerSet, faceUnion, Finset.sup_insert, Finset.sup_singleton,
    ReversalOuterFaceLocality.ordinaryOuterFaces]

private theorem endpoint_union (P : MorphismProperty SSet.{u})
    [P.IsStableUnderCobaseChange]
    (hcancel : ∀ {A B C : SSet.{u}} (f : A ⟶ B) (g : B ⟶ C),
      Mono g → P f → P (f ≫ g) → P g)
    (hOuter : ∀ m : ℕ, P (faceUnion.{u} (outerSet m)).ι) :
    ∀ (m : ℕ) (S : Finset (Fin (m + 3))) (k : Fin (m + 3)),
      k ∉ S → k ≠ 0 → k ≠ Fin.last (m + 2) →
      (0 : Fin (m + 3)) ∈ S → Fin.last (m + 2) ∈ S →
        P (faceUnion.{u} S).ι := by
  intro m
  induction m with
  | zero =>
    intro S k hk hk0 hklast h0 hlast
    by_cases hsub : S ⊆ outerSet 0
    · have heq : S = outerSet 0 := by
        apply Finset.Subset.antisymm hsub
        intro j hj
        simp only [outerSet, Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl
        · exact h0
        · exact hlast
      rw [heq]
      exact hOuter 0
    · obtain ⟨i, hiS, hiOuter⟩ := Finset.not_subset.mp hsub
      have hi0 : i ≠ 0 := by
        intro h
        subst i
        exact hiOuter (by simp [outerSet])
      have hiLast : i ≠ Fin.last 2 := by
        intro h
        subst i
        exact hiOuter (by simp [outerSet])
      have hik : i = k := by
        apply Fin.ext
        have hiLt := i.isLt
        have hkLt := k.isLt
        have hi0val : i.val ≠ 0 := by
          intro h
          exact hi0 (Fin.ext h)
        have hiLastVal : i.val ≠ 2 := by
          intro h
          apply hiLast
          apply Fin.ext
          simpa using h
        have hk0val : k.val ≠ 0 := by
          intro h
          exact hk0 (Fin.ext h)
        have hkLastVal : k.val ≠ 2 := by
          intro h
          apply hklast
          apply Fin.ext
          simpa using h
        omega
      exact False.elim (hk (hik ▸ hiS))
  | succ m ih =>
    intro S
    refine Finset.strongInductionOn S ?_
    intro S ihS k hk hk0 hklast h0 hlast
    by_cases hsub : S ⊆ outerSet (m + 1)
    · have heq : S = outerSet (m + 1) := by
        apply Finset.Subset.antisymm hsub
        intro j hj
        simp only [outerSet, Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl
        · exact h0
        · exact hlast
      rw [heq]
      exact hOuter (m + 1)
    · obtain ⟨i, hiS, hiOuter⟩ := Finset.not_subset.mp hsub
      have hi0 : i ≠ 0 := by
        intro h
        subst i
        exact hiOuter (by simp [outerSet])
      have hiLast : i ≠ Fin.last (m + 3) := by
        intro h
        subst i
        exact hiOuter (by simp [outerSet])
      let T := S.erase i
      have hiT : i ∉ T := Finset.notMem_erase i S
      have hkT : k ∉ T := fun h ↦ hk (Finset.mem_of_mem_erase h)
      have h0T : (0 : Fin (m + 4)) ∈ T :=
        Finset.mem_erase.mpr ⟨Ne.symm hi0, h0⟩
      have hlastT : Fin.last (m + 3) ∈ T :=
        Finset.mem_erase.mpr ⟨Ne.symm hiLast, hlast⟩
      have hOld : P (faceUnion.{u} T).ι :=
        ihS T (Finset.erase_ssubset hiS) k hkT hk0 hklast h0T hlastT
      have hki : k ≠ i := by
        intro h
        exact hk (h ▸ hiS)
      obtain ⟨l, hl, hlMissing⟩ := faceIndices_missing T i k hkT hki
      have hzero : (0 : Fin (m + 3)) ∈ faceIndices T i := by
        simp only [faceIndices, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [Fin.succAbove_ne_zero_zero hi0]
        exact h0T
      have hfinal : Fin.last (m + 2) ∈ faceIndices T i := by
        simp only [faceIndices, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [Fin.succAbove_ne_last_last hiLast]
        exact hlastT
      have hl0 : l ≠ 0 := by
        intro h
        subst l
        rw [Fin.succAbove_ne_zero_zero hi0] at hl
        exact hk0 hl.symm
      have hlLast : l ≠ Fin.last (m + 2) := by
        intro h
        subst l
        rw [Fin.succAbove_ne_last_last hiLast] at hl
        exact hklast hl.symm
      have hPre : P (faceUnion.{u} (faceIndices T i)).ι :=
        ih (faceIndices T i) l hlMissing hl0 hlLast hzero hfinal
      have hPre' : P (((faceUnion.{u} T).preimage (SSet.stdSimplex.δ i)).ι) := by
        rw [faceUnion_preimage_face T i hiT]
        exact hPre
      let a := SSet.Subcomplex.homOfLE (show faceUnion.{u} T ≤
          faceUnion (insert i T) from faceUnion_insert T i ▸ le_sup_left)
      have ha : P a := P.of_isPushout (faceUnion_attachment_isPushout T i) hPre'
      have hOld' : P (a ≫ (faceUnion.{u} (insert i T)).ι) := by
        change P ((faceUnion.{u} T).ι)
        exact hOld
      have hNew : P (faceUnion.{u} (insert i T)).ι :=
        hcancel a _ (by infer_instance) ha hOld'
      change P (faceUnion.{u} (insert i (S.erase i))).ι at hNew
      rw [Finset.insert_erase hiS] at hNew
      exact hNew

/-- Cobase closure and cancellation transfer the two-outer-face test to
every literal inner-horn inclusion, in every dimension at least two. -/
theorem innerHorn_of_outerFaces (P : MorphismProperty SSet.{u})
    [P.IsStableUnderCobaseChange]
    (hcancel : ∀ {A B C : SSet.{u}} (f : A ⟶ B) (g : B ⟶ C),
      Mono g → P f → P (f ≫ g) → P g)
    (hOuter : ∀ m : ℕ,
      P (ReversalOuterFaceLocality.ordinaryOuterFaces.{u} m).ι)
    (m : ℕ) (k : Fin (m + 3))
    (hk0 : k ≠ 0) (hkLast : k ≠ Fin.last (m + 2)) :
    P (SSet.horn (m + 2) k).ι := by
  have hOuter' : ∀ q : ℕ, P (faceUnion.{u} (outerSet q)).ι := by
    intro q
    rw [outerSet_faceUnion]
    exact hOuter q
  have h := endpoint_union P hcancel hOuter' m (Finset.univ.erase k) k
    (Finset.notMem_erase k _) hk0 hkLast
    (Finset.mem_erase.mpr ⟨Ne.symm hk0, Finset.mem_univ _⟩)
    (Finset.mem_erase.mpr ⟨Ne.symm hkLast, Finset.mem_univ _⟩)
  rw [faceUnion_erase_eq_horn] at h
  exact h

#print axioms outerSet_faceUnion
#print axioms innerHorn_of_outerFaces

end
end DaggerModels.PartII.OrdinaryInnerHornFromOuterFaces
