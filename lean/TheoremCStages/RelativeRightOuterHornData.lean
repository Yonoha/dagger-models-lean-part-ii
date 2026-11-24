import RelativeBoundaryTargetLifting
import OriginalRightOuterHornFilling

/-!
# The prescribed base simplex as an edge of the relative boundary target

The original right outer horn determines the source boundary and the fixed
coslice target. A compatible whole simplex in the base determines the second
coordinate of an edge of the actual relative pullback. Both coordinates are
retained as exact one-simplex equations.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial
open DaggerOriginalOrdinalJoinLeft DaggerOriginalSimplexCoslice
open DaggerOriginalCosliceOneHornLifting DaggerOriginalLeftMappingFunctoriality
open DaggerOriginalJoinedHornGeometry DaggerOriginalJoinedBoundaryRestriction
open DaggerOriginalJoinedHornPrefix
open DaggerOriginalJoinedBoundaryProjection DaggerOriginalRightOuterHornInclusions
open DaggerOriginalRightOuterHornData DaggerOriginalRelativeCosliceRestrictionLifting

universe u

namespace DaggerOriginalRelativeRightOuterHornData

noncomputable section

/-- A compatible base simplex gives the actual relative edge with the prescribed target.
Its first projection is the whole original boundary edge, and its second
projection is exactly the supplied base simplex, regarded as a joined edge. -/
theorem relative_right_outer_boundary_edge {C D : SSet.{u}} (p : C ⟶ D) (k : ℕ)
    (φ : (Λ[k + 2, Fin.last (k + 2)] : SSet.{u}) ⟶ C)
    (μD : (Δ[k + 2] : SSet.{u}) ⟶ D)
    (w : φ ≫ p = Λ[k + 2, Fin.last (k + 2)].ι ≫ μD) :
    ∃ a : (relativeBoundaryTarget p k (rightOuterPrefix k φ)).obj (op ⦋0⦌),
      ∃ e : SSet.Edge a
          ((relativeCosliceRestriction p k (rightOuterPrefix k φ)).app (op ⦋0⦌)
            (rightOuterCosliceVertex k φ)),
        (pullback.fst (boundaryJoinedMap p k)
          (cosliceBoundaryRestriction k D
            (p.app (op ⦋k⦌) (rightOuterPrefix k φ)))).app (op ⦋1⦌) e.edge =
            (rightOuterBoundaryEdge k φ).edge ∧
          ((pullback.snd (boundaryJoinedMap p k)
            (cosliceBoundaryRestriction k D
              (p.app (op ⦋k⦌) (rightOuterPrefix k φ)))).app (op ⦋1⦌) e.edge).val =
                SSet.yonedaEquiv μD := by
  let f := rightOuterPrefix k φ
  let b := rightOuterCosliceVertex k φ
  let r : (joinedPresheaf ⦋k⦌ D).obj (op ⦋1⦌) :=
    (SSet.yonedaEquiv (X := D) (n := ⦋k + 2⦌)) μD
  let t := (cosliceMap p ⦋k⦌ f).app (op ⦋0⦌) b
  have hface : SSet.stdSimplex.map
        ((ordinalJoinLeft ⦋k⦌).map (SimplexCategory.δ (n := 0) 0)) ≫ μD =
      (rightOuterJoinedFaceInclusion k ≫ φ) ≫ p := by
    rw [← rightOuterJoinedFaceInclusion_comp, Category.assoc, ← w, ← Category.assoc]
  have htarget : (joinedPresheaf ⦋k⦌ D).δ 0 r = t.val := by
    have hv := congrArg (SSet.yonedaEquiv (X := D) (n := ⦋k + 1⦌)) hface
    rw [yonedaEquiv_precomp_operator, SSet.yonedaEquiv_comp] at hv
    exact hv
  have hr : r ∈ (prefixFiber ⦋k⦌ D (p.app (op ⦋k⦌) f)).obj (op ⦋1⦌) := by
    have h := prefix_operator_eq ⦋k⦌ (SimplexCategory.δ (n := 0) 0) r
    change D.map (AugmentedSimplexCategory.inl' ⦋k⦌ ⦋0⦌).op
      ((joinedPresheaf ⦋k⦌ D).δ 0 r) = _ at h
    rw [htarget] at h
    exact h.symm.trans t.property
  let q : (simplexCoslice ⦋k⦌ D (p.app (op ⦋k⦌) f)).obj (op ⦋1⦌) := ⟨r, hr⟩
  let A : (Δ[1] : SSet.{u}) ⟶ boundaryJoinedPresheaf k C :=
    SSet.yonedaEquiv.symm (rightOuterBoundaryData k φ)
  let B : (Δ[1] : SSet.{u}) ⟶ simplexCoslice ⦋k⦌ D (p.app (op ⦋k⦌) f) :=
    SSet.yonedaEquiv.symm q
  have hAB : A ≫ boundaryJoinedMap p k =
      B ≫ cosliceBoundaryRestriction k D (p.app (op ⦋k⦌) f) := by
    apply (SSet.yonedaEquiv (X := boundaryJoinedPresheaf k D) (n := ⦋1⦌)).injective
    rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp]
    change (boundaryJoinedMap p k).app (op ⦋1⦌)
        (SSet.yonedaEquiv (SSet.yonedaEquiv.symm (rightOuterBoundaryData k φ))) =
      (cosliceBoundaryRestriction k D (p.app (op ⦋k⦌) f)).app (op ⦋1⦌)
        (SSet.yonedaEquiv (SSet.yonedaEquiv.symm q))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    change (rightOuterBoundaryInclusion k ≫ φ) ≫ p =
      (prefixBoundary k 1).ι ≫ SSet.yonedaEquiv.symm (SSet.yonedaEquiv μD)
    rw [Equiv.symm_apply_apply, Category.assoc, w,
      ← Category.assoc, rightOuterBoundaryInclusion_comp]
  let E := relativeBoundaryTarget p k f
  let η : (Δ[1] : SSet.{u}) ⟶ E := pullback.lift A B hAB
  have hηA : η ≫ pullback.fst _ _ = A := pullback.lift_fst _ _ _
  have hηB : η ≫ pullback.snd _ _ = B := pullback.lift_snd _ _ _
  have hA0 : SSet.stdSimplex.δ 0 ≫ A =
      SSet.yonedaEquiv.symm
        ((cosliceBoundaryRestriction k C f).app (op ⦋0⦌) b) := by
    apply (SSet.yonedaEquiv (X := boundaryJoinedPresheaf k C) (n := ⦋0⦌)).injective
    have ho := yonedaEquiv_precomp_operator A (SimplexCategory.δ (n := 0) 0)
    change SSet.yonedaEquiv (SSet.stdSimplex.δ 0 ≫ A) = _ at ho
    rw [ho]
    simpa only [A, Equiv.apply_symm_apply] using rightOuterBoundaryData_target k φ
  have hB0 : SSet.stdSimplex.δ 0 ≫ B = SSet.yonedaEquiv.symm t := by
    apply (SSet.yonedaEquiv (X := simplexCoslice ⦋k⦌ D
      (p.app (op ⦋k⦌) f)) (n := ⦋0⦌)).injective
    have ho := yonedaEquiv_precomp_operator B (SimplexCategory.δ (n := 0) 0)
    change SSet.yonedaEquiv (SSet.stdSimplex.δ 0 ≫ B) = _ at ho
    rw [ho]
    have hq : (simplexCoslice ⦋k⦌ D (p.app (op ⦋k⦌) f)).δ 0 q = t :=
      Subtype.ext htarget
    simpa only [B, Equiv.apply_symm_apply] using hq
  have hpoint : (SSet.yonedaEquiv (X := E) (n := ⦋0⦌))
      ((SSet.yonedaEquiv (X := E) (n := ⦋0⦌)).symm
        ((relativeCosliceRestriction p k f).app (op ⦋0⦌) b)) =
      (relativeCosliceRestriction p k f).app (op ⦋0⦌) b :=
    Equiv.apply_symm_apply _ _
  have hη0 : SSet.stdSimplex.δ 0 ≫ η =
      SSet.yonedaEquiv.symm
        ((relativeCosliceRestriction p k f).app (op ⦋0⦌) b) := by
    apply pullback.hom_ext
    · rw [Category.assoc, hηA, hA0]
      apply (SSet.yonedaEquiv (X := boundaryJoinedPresheaf k C)
        (n := ⦋0⦌)).injective
      simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
      have hf : relativeCosliceRestriction p k f ≫ pullback.fst _ _ =
          cosliceBoundaryRestriction k C f := pullback.lift_fst _ _ _
      have he := congrArg (fun z ↦ z.app (op ⦋0⦌) b) hf
      exact he.symm.trans (congrArg
        ((pullback.fst (boundaryJoinedMap p k)
          (cosliceBoundaryRestriction k D (p.app (op ⦋k⦌) f))).app (op ⦋0⦌))
            hpoint).symm
    · rw [Category.assoc, hηB, hB0]
      apply (SSet.yonedaEquiv (X := simplexCoslice ⦋k⦌ D
        (p.app (op ⦋k⦌) f)) (n := ⦋0⦌)).injective
      simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
      have hf : relativeCosliceRestriction p k f ≫ pullback.snd _ _ =
          cosliceMap p ⦋k⦌ f := pullback.lift_snd _ _ _
      have he := congrArg (fun z ↦ z.app (op ⦋0⦌) b) hf
      exact he.symm.trans (congrArg
        ((pullback.snd (boundaryJoinedMap p k)
          (cosliceBoundaryRestriction k D (p.app (op ⦋k⦌) f))).app (op ⦋0⦌))
            hpoint).symm
  let s := SSet.yonedaEquiv η
  have hs0 : E.δ 0 s = (relativeCosliceRestriction p k f).app (op ⦋0⦌) b := by
    have h := congrArg SSet.yonedaEquiv hη0
    have ho := yonedaEquiv_precomp_operator η (SimplexCategory.δ (n := 0) 0)
    change SSet.yonedaEquiv (SSet.stdSimplex.δ 0 ≫ η) = _ at ho
    rw [ho, Equiv.apply_symm_apply] at h
    exact h
  refine ⟨E.δ 1 s, ⟨s, rfl, hs0⟩, ?_, ?_⟩
  · have h := congrArg SSet.yonedaEquiv hηA
    rw [SSet.yonedaEquiv_comp] at h
    exact h.trans (Equiv.apply_symm_apply _ _)
  · have h := congrArg SSet.yonedaEquiv hηB
    rw [SSet.yonedaEquiv_comp] at h
    have hq := h.trans (Equiv.apply_symm_apply _ _)
    exact congrArg Subtype.val hq

#print axioms relative_right_outer_boundary_edge

end

end DaggerOriginalRelativeRightOuterHornData
