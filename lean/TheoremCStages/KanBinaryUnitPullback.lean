import TopCatModelCategory.ModelCategorySSet
import TopCatModelCategory.SSet.Fiber

/-!
# A strict binary Segal comparison gives the unit pullback comparison

The binary comparison is an actual Kan trivial fibration onto the pullback
of two endpoint maps. Inserting a split unit into its second edge gives a
pullback square for the binary comparison itself. Its base change is weak,
and the original unit insertion is a section of that weak map.

This is the model-category argument for the first square of Rezk 12.4;
the actual simplicial-space face and degeneracy operators are a separate
application, not additional assumptions on the original Theorem C.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.KanBinaryUnitPullback

noncomputable section

variable {O A B : SSet.{u}} (d0 d1 : A ⟶ O) (s : O ⟶ A)
    (hs : s ≫ d0 = 𝟙 O) (r0 r2 : B ⟶ A)
    (q : B ⟶ pullback d1 d0)
    (hfst : q ≫ pullback.fst d1 d0 = r0)
    (hsnd : q ≫ pullback.snd d1 d0 = r2)

/-- The actual pair consisting of an edge and the identity at its source. -/
def unitSpan : A ⟶ pullback d1 d0 :=
  pullback.lift (𝟙 A) (d1 ≫ s) (by simp only [Category.assoc, hs,
    Category.id_comp, Category.comp_id])

include hfst hsnd in
private theorem edge_comm : r0 ≫ d1 = r2 ≫ d0 := by
  rw [← hfst, ← hsnd, Category.assoc, Category.assoc, pullback.condition]

/-- Forget the inserted unit and retain the other edge of the same triangle. -/
def otherEdge : pullback r2 s ⟶ A := pullback.fst r2 s ≫ r0

include hfst hsnd in
/-- The strict unit pullback is also the base change of the binary comparison. -/
theorem comparison_isPullback :
    IsPullback (pullback.fst r2 s) (otherEdge (s := s) (r0 := r0) (r2 := r2))
      q (unitSpan d0 d1 s hs) := by
  have hcomm := edge_comm d0 d1 r0 r2 q hfst hsnd
  have hm : Mono s := mono_of_mono_fac hs
  have : Mono (pullback.fst r2 s) := inferInstance
  have hother : otherEdge (s := s) (r0 := r0) (r2 := r2) ≫ d1 = pullback.snd r2 s := by
    dsimp only [otherEdge]
    rw [Category.assoc, hcomm, ← Category.assoc, pullback.condition,
      Category.assoc, hs, Category.comp_id]
  refine {
    w := ?_
    isLimit' := ?_ }
  · apply pullback.hom_ext
    · simp only [Category.assoc, hfst, unitSpan, pullback.lift_fst,
        Category.comp_id, otherEdge]
    · simp only [Category.assoc, hsnd, unitSpan, pullback.lift_snd]
      rw [← Category.assoc, hother, pullback.condition]
  · refine ⟨PullbackCone.IsLimit.mk _ (fun t ↦ pullback.lift t.fst (t.snd ≫ d1) ?_)
      (fun t ↦ by simp only [pullback.lift_fst]) (fun t ↦ ?_) (fun t m hm _ ↦ ?_)⟩
    · have h := congrArg (fun k ↦ k ≫ pullback.snd d1 d0) t.condition
      simpa only [Category.assoc, hsnd, unitSpan, pullback.lift_snd] using h
    · dsimp only [otherEdge]
      rw [← Category.assoc, pullback.lift_fst]
      have h := congrArg (fun k ↦ k ≫ pullback.fst d1 d0) t.condition
      simpa only [Category.assoc, hfst, unitSpan, pullback.lift_fst,
        Category.comp_id] using h
    · apply (cancel_mono (pullback.fst r2 s)).mp
      simpa only [pullback.lift_fst] using hm

/-- The exact original unit comparison into its strict face pullback. -/
def unitComparison (h : A ⟶ B) (h2 : h ≫ r2 = d1 ≫ s) : A ⟶ pullback r2 s :=
  pullback.lift h d1 h2

include hs hfst hsnd in
/-- A binary Kan trivial fibration makes this literal unit comparison weak. -/
theorem unitComparison_weak (h : A ⟶ B) (h0 : h ≫ r0 = 𝟙 A)
    (h2 : h ≫ r2 = d1 ≫ s) [Fibration q] [WeakEquivalence q] :
    WeakEquivalence (unitComparison d1 s r2 h h2) := by
  have : WeakEquivalence (otherEdge (s := s) (r0 := r0) (r2 := r2)) :=
    SSet.modelCategoryQuillen.weakEquivalence_of_fibration_of_isPullback
      (comparison_isPullback d0 d1 s hs r0 r2 q hfst hsnd)
  have fac : unitComparison d1 s r2 h h2 ≫ otherEdge (s := s) (r0 := r0) (r2 := r2) = 𝟙 A := by
    dsimp only [unitComparison, otherEdge]
    rw [← Category.assoc, pullback.lift_fst, h0]
  exact weakEquivalence_of_postcomp_of_fac fac

#print axioms comparison_isPullback
#print axioms unitComparison_weak

end

end DaggerModels.PartII.KanBinaryUnitPullback
