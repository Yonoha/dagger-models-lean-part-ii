import DaggerModelsPartII.KanLeftProper
import DaggerModelsPartII.LeftProperPushoutComparison
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-!
# Finite comparison of subcomplexes along their preimages
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u v

namespace DaggerModels.PartII.JTFiniteSubcomplexPreimageGluing

open SSet.Subcomplex

variable {X Y : SSet.{u}} (f : X ⟶ Y)

/-- A restriction to a subcomplex commutes with passage to a larger
subcomplex. -/
@[reassoc]
theorem fromPreimage_homOfLE {A B : Y.Subcomplex} (h : A ≤ B) :
    SSet.Subcomplex.homOfLE (show A.preimage f ≤ B.preimage f from
      fun n ↦ Set.preimage_mono (h n)) ≫ B.fromPreimage f =
      A.fromPreimage f ≫ SSet.Subcomplex.homOfLE h := by
  rw [← cancel_mono B.ι]
  simp only [Category.assoc, fromPreimage_ι, homOfLE_ι, homOfLE_ι_assoc]

/-- Weak preimage comparisons glue on the exact intersection. -/
theorem weak_sup (A B : Y.Subcomplex)
    (hA : WeakEquivalence (A.fromPreimage f))
    (hB : WeakEquivalence (B.fromPreimage f))
    (hI : WeakEquivalence ((A ⊓ B).fromPreimage f)) :
    WeakEquivalence ((A ⊔ B).fromPreimage f) := by
  let sq : BicartSq (A ⊓ B) A B (A ⊔ B) := ⟨rfl, rfl⟩
  let sq' : BicartSq ((A ⊓ B).preimage f) (A.preimage f) (B.preimage f)
      ((A ⊔ B).preimage f) :=
    ⟨(preimage_max A B f).symm, (preimage_min A B f).symm⟩
  exact (weakEquivalence_iff _).mpr (weak_of_pushoutComparison
    (fun s h₁ h₂ ↦ kanLeftProper s h₁ h₂)
    sq'.isPushout sq.isPushout
    ((cofibration_iff _).mp (SSet.modelCategoryQuillen.cofibration_of_mono _))
    ((cofibration_iff _).mp (SSet.modelCategoryQuillen.cofibration_of_mono _))
    ((A ⊓ B).fromPreimage f) (A.fromPreimage f) (B.fromPreimage f) ((A ⊔ B).fromPreimage f)
    (fromPreimage_homOfLE f sq.le₁₂) (fromPreimage_homOfLE f sq.le₁₃)
    (fromPreimage_homOfLE f sq.le₂₄) (fromPreimage_homOfLE f sq.le₃₄)
    ((weakEquivalence_iff _).mp hI) ((weakEquivalence_iff _).mp hA)
    ((weakEquivalence_iff _).mp hB))

private theorem weak_bot : WeakEquivalence ((⊥ : Y.Subcomplex).fromPreimage f) := by
  have h : (⊥ : Y.Subcomplex).preimage f = ⊥ := rfl
  let hi : IsInitial (((⊥ : Y.Subcomplex).preimage f) : SSet.{u}) :=
    h.symm ▸ isInitialBot
  have he : (⊥ : Y.Subcomplex).fromPreimage f =
      (hi.uniqueUpToIso isInitialBot).hom := hi.hom_ext _ _
  rw [he]
  infer_instance

/-- If the preimage comparisons are weak on every nonempty finite
intersection, the comparison on the union is weak. The auxiliary
intersection allows one induction to handle overlaps with earlier faces. -/
theorem weak_inf_finset_sup {ι : Type v} (F : ι → Y.Subcomplex) (s : Finset ι)
    (B : Y.Subcomplex)
    (h : ∀ t ⊆ s, t.Nonempty → WeakEquivalence ((B ⊓ t.inf F).fromPreimage f)) :
    WeakEquivalence ((B ⊓ s.sup F).fromPreimage f) := by
  classical
  induction s using Finset.induction_on generalizing B with
  | empty =>
    have h₀ : (B ⊓ (∅ : Finset ι).sup F : Y.Subcomplex) = ⊥ := by simp
    rw [h₀]
    exact weak_bot f
  | @insert i s hi ih =>
    have h₀ : (B ⊓ (insert i s).sup F : Y.Subcomplex) =
        (B ⊓ F i) ⊔ (B ⊓ s.sup F) := by
      rw [Finset.sup_insert]
      ext q a
      change (a ∈ B.obj q ∧ (a ∈ (F i).obj q ∨ a ∈ (s.sup F).obj q)) ↔
        (a ∈ B.obj q ∧ a ∈ (F i).obj q) ∨ (a ∈ B.obj q ∧ a ∈ (s.sup F).obj q)
      tauto
    rw [h₀]
    apply weak_sup
    · have h₀ := h {i} (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self i s))
        (Finset.singleton_nonempty i)
      have he : (({i} : Finset ι).inf F : Y.Subcomplex) = F i := Finset.inf_singleton
      rw [he] at h₀
      exact h₀
    · apply ih B
      intro t ht hne
      exact h t (ht.trans (Finset.subset_insert i s)) hne
    · have h₁ : ((B ⊓ F i) ⊓ (B ⊓ s.sup F) : Y.Subcomplex) = (B ⊓ F i) ⊓ s.sup F := by
        calc
          _ = ((B ⊓ B) ⊓ F i) ⊓ s.sup F := by ac_rfl
          _ = _ := by rw [inf_idem]
      rw [h₁]
      apply ih (B ⊓ F i)
      intro t ht _
      have he : ((B ⊓ F i) ⊓ t.inf F : Y.Subcomplex) = B ⊓ (insert i t).inf F := by
        rw [Finset.inf_insert, inf_assoc]
      rw [he]
      exact h (insert i t) (Finset.insert_subset_insert i ht) (Finset.insert_nonempty i t)

/-- Comparison on the union of a finite cover follows from comparison on
all its nonempty intersections. -/
theorem weak_finset_sup {ι : Type v} (F : ι → Y.Subcomplex) (s : Finset ι)
    (h : ∀ t ⊆ s, t.Nonempty → WeakEquivalence ((t.inf F).fromPreimage f)) :
    WeakEquivalence ((s.sup F).fromPreimage f) := by
  have h' := weak_inf_finset_sup f F s ⊤ (by
    intro t ht hne
    have he : (⊤ ⊓ t.inf F : Y.Subcomplex) = t.inf F := top_inf_eq _
    rw [he]
    exact h t ht hne)
  have he : (⊤ ⊓ s.sup F : Y.Subcomplex) = s.sup F := top_inf_eq _
  rwa [he] at h'

end DaggerModels.PartII.JTFiniteSubcomplexPreimageGluing
