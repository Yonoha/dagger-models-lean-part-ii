import RelativeCosliceInnerFibrationLifting
import OriginalLeftMappingFunctoriality
import OriginalCosliceLeftHornLifting
import OriginalCosliceOneHornLifting

/-!
# Relative restriction of an original fixed-prefix coslice

The target keeps both the original boundary in `C` and the prescribed full
joined simplex in `D`. Its pullback equation is converted into the exact
boundary and coface equations for relative inner-horn filling.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial Limits
open DaggerOriginalSimplexCoslice DaggerOriginalOrdinalJoinLeft
open DaggerOriginalJoinedHornGeometry DaggerOriginalJoinedHornPrefix
open DaggerOriginalJoinedPrefixBoundaryFunctor
open DaggerOriginalJoinedCofaces DaggerOriginalJoinedBoundaryRestriction
open DaggerOriginalJoinedSuffixFaceMaps DaggerOriginalLeftMappingFunctoriality
open DaggerOriginalCosliceOneHornLifting
open DaggerOriginalRelativeCosliceInnerFibrationLifting
open DaggerNativeInnerHornFactorization

universe u

namespace DaggerOriginalRelativeCosliceRestrictionLifting

noncomputable section

/-- Postcomposition on the actual presheaf of joined prefix-boundary maps. -/
def boundaryJoinedMap {C D : SSet.{u}} (p : C ⟶ D) (k : ℕ) :
    boundaryJoinedPresheaf k C ⟶ boundaryJoinedPresheaf k D where
  app _ β := β ≫ p
  naturality _ _ a := by
    funext β
    change prefixBoundaryMap k a.unop ≫ (β ≫ p) =
      (prefixBoundaryMap k a.unop ≫ β) ≫ p
    exact (Category.assoc _ _ _).symm

/-- Boundary restriction commutes with the literal postcomposition map of coslices. -/
theorem cosliceMap_boundary {C D : SSet.{u}} (p : C ⟶ D) (k : ℕ)
    (f : C.obj (op ⦋k⦌)) :
    cosliceBoundaryRestriction k C f ≫ boundaryJoinedMap p k =
      cosliceMap p ⦋k⦌ f ≫
        cosliceBoundaryRestriction k D (p.app (op ⦋k⦌) f) := by
  ext q s
  change ((prefixBoundary k q.unop.len).ι ≫
      (SSet.yonedaEquiv (X := C) (n := ⦋k + q.unop.len + 1⦌)).symm s.val) ≫ p =
    (prefixBoundary k q.unop.len).ι ≫
      (SSet.yonedaEquiv (X := D) (n := ⦋k + q.unop.len + 1⦌)).symm
        (p.app (op ⦋k + q.unop.len + 1⦌) s.val)
  rw [Category.assoc, SSet.yonedaEquiv_symm_comp]

/-- The unchanged relative target from Kerodon's coslice argument. -/
def relativeBoundaryTarget {C D : SSet.{u}} (p : C ⟶ D) (k : ℕ)
    (f : C.obj (op ⦋k⦌)) : SSet.{u} :=
  pullback (boundaryJoinedMap p k)
    (cosliceBoundaryRestriction k D (p.app (op ⦋k⦌) f))

/-- The relative coslice restriction retaining both original target coordinates. -/
def relativeCosliceRestriction {C D : SSet.{u}} (p : C ⟶ D) (k : ℕ)
    (f : C.obj (op ⦋k⦌)) :
    simplexCoslice ⦋k⦌ C f ⟶ relativeBoundaryTarget p k f :=
  pullback.lift (cosliceBoundaryRestriction k C f) (cosliceMap p ⦋k⦌ f)
    (cosliceMap_boundary p k f)

/-- The q-relative fixed-prefix coslice restriction lifts every nonfinal horn. -/
theorem relativeCosliceRestriction_hasLiftingProperty {C D : SSet.{u}}
    (p : C ⟶ D) (hp : innerFibrations p) (k : ℕ)
    (f : C.obj (op ⦋k⦌)) (n : ℕ) (i : Fin (n + 2))
    (hi : i < Fin.last (n + 1)) :
    HasLiftingProperty (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι
      (relativeCosliceRestriction p k f) where
  sq_hasLift := by
    intro φ β sq
    let βC : (Δ[n + 1] : SSet.{u}) ⟶ boundaryJoinedPresheaf k C :=
      β ≫ pullback.fst _ _
    let βD : (Δ[n + 1] : SSet.{u}) ⟶
        simplexCoslice ⦋k⦌ D (p.app (op ⦋k⦌) f) := β ≫ pullback.snd _ _
    have hφC : φ ≫ cosliceBoundaryRestriction k C f = Λ[n + 1, i].ι ≫ βC := by
      have h := congrArg (fun t ↦ t ≫ pullback.fst _ _) sq.w
      simpa only [Category.assoc, relativeCosliceRestriction, pullback.lift_fst] using h
    have hφD : φ ≫ cosliceMap p ⦋k⦌ f = Λ[n + 1, i].ι ≫ βD := by
      have h := congrArg (fun t ↦ t ≫ pullback.snd _ _) sq.w
      simpa only [Category.assoc, relativeCosliceRestriction, pullback.lift_snd] using h
    have hφraw : (φ ≫ (prefixFiber ⦋k⦌ C f).ι) ≫
        joinedBoundaryRestriction k C = Λ[n + 1, i].ι ≫ βC := by
      rw [Category.assoc]
      exact hφC
    let bD := (SSet.yonedaEquiv (X := simplexCoslice ⦋k⦌ D
      (p.app (op ⦋k⦌) f)) (n := ⦋n + 1⦌)) βD
    let μD : (Δ[k + (n + 1) + 1] : SSet.{u}) ⟶ D :=
      (SSet.yonedaEquiv (X := D) (n := ⦋k + (n + 1) + 1⦌)).symm bD.val
    have hβ : βC ≫ boundaryJoinedMap p k =
        βD ≫ cosliceBoundaryRestriction k D (p.app (op ⦋k⦌) f) := by
      dsimp [βC, βD]
      simp only [Category.assoc, pullback.condition]
    have hboundary : SSet.yonedaEquiv βC ≫ p =
        (prefixBoundary k (n + 1)).ι ≫ μD := by
      have hv := congrArg
        (SSet.yonedaEquiv (X := boundaryJoinedPresheaf k D) (n := ⦋n + 1⦌)) hβ
      rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp] at hv
      change SSet.yonedaEquiv βC ≫ p =
        (prefixBoundary k (n + 1)).ι ≫ μD at hv
      exact hv
    have hface (j : Fin (n + 2)) (hj : j ≠ i) :
        joinedHornCoface k n i j hj
            (φ ≫ (prefixFiber ⦋k⦌ C f).ι) ≫ p =
          SSet.stdSimplex.δ (suffixIndex k (n + 1) j) ≫ μD := by
      have hcoface : (SSet.horn.ι i j hj ≫ φ) ≫ cosliceMap p ⦋k⦌ f =
          SSet.stdSimplex.δ j ≫ βD := by
        rw [Category.assoc, hφD, ← Category.assoc, SSet.horn.ι_ι]
      have hv := congrArg
        (SSet.yonedaEquiv (X := simplexCoslice ⦋k⦌ D
          (p.app (op ⦋k⦌) f)) (n := ⦋n⦌)) hcoface
      have ho := yonedaEquiv_precomp_operator βD (SimplexCategory.δ j)
      change SSet.yonedaEquiv (SSet.stdSimplex.δ j ≫ βD) = _ at ho
      rw [SSet.yonedaEquiv_comp, ho] at hv
      change (cosliceMap p ⦋k⦌ f).app (op ⦋n⦌)
          (SSet.yonedaEquiv (SSet.horn.ι i j hj ≫ φ)) =
        (simplexCoslice ⦋k⦌ D (p.app (op ⦋k⦌) f)).map
          (SimplexCategory.δ j).op bD at hv
      have hval := congrArg Subtype.val hv
      apply (SSet.yonedaEquiv (X := D) (n := ⦋k + n + 1⦌)).injective
      dsimp only [joinedHornCoface]
      rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
      have hμ := yonedaEquiv_precomp_operator μD
        (SimplexCategory.δ (suffixIndex k (n + 1) j))
      change SSet.yonedaEquiv
        (SSet.stdSimplex.δ (suffixIndex k (n + 1) j) ≫ μD) = _ at hμ
      calc
        _ = D.map (SimplexCategory.δ (suffixIndex k (n + 1) j)).op bD.val := by
          change p.app (op ⦋k + n + 1⦌)
              ((SSet.yonedaEquiv (X := joinedPresheaf ⦋k⦌ C) (n := ⦋n⦌))
                (SSet.horn.ι i j hj ≫ φ ≫ (prefixFiber ⦋k⦌ C f).ι)) = _
          rw [← joinMap_coface]
          exact hval
        _ = _ := by
          have hμ' : SSet.yonedaEquiv μD = bD.val := Equiv.apply_symm_apply _ _
          exact (congrArg (D.map
            (SimplexCategory.δ (suffixIndex k (n + 1) j)).op) hμ').symm.trans hμ.symm
    obtain ⟨μC, hμboundary, hμfaces, hμbase⟩ :=
      joined_horn_extension_over p hp k n i hi
        (φ ≫ (prefixFiber ⦋k⦌ C f).ι) βC hφraw μD hboundary hface
    let r : (joinedPresheaf ⦋k⦌ C).obj (op ⦋n + 1⦌) :=
      (SSet.yonedaEquiv (X := C) (n := ⦋k + (n + 1) + 1⦌)) μC
    let τ : (Δ[n + 1] : SSet.{u}) ⟶ joinedPresheaf ⦋k⦌ C :=
      SSet.yonedaEquiv.symm r
    have hτsource (l : Fin (n + 2)) (hl : l ≠ i) :
        SSet.stdSimplex.δ l ≫ τ =
          SSet.horn.ι i l hl ≫ (φ ≫ (prefixFiber ⦋k⦌ C f).ι) := by
      apply (SSet.yonedaEquiv (X := joinedPresheaf ⦋k⦌ C) (n := ⦋n⦌)).injective
      have hv := congrArg (SSet.yonedaEquiv (X := C) (n := ⦋k + n + 1⦌))
        (hμfaces l hl)
      change SSet.yonedaEquiv
          (SSet.stdSimplex.δ (suffixIndex k (n + 1) l) ≫ μC) =
        (SSet.yonedaEquiv (X := C) (n := ⦋k + n + 1⦌))
          ((SSet.yonedaEquiv (X := C) (n := ⦋k + n + 1⦌)).symm
            ((SSet.yonedaEquiv (X := joinedPresheaf ⦋k⦌ C) (n := ⦋n⦌))
              (SSet.horn.ι i l hl ≫ (φ ≫ (prefixFiber ⦋k⦌ C f).ι)))) at hv
      rw [Equiv.apply_symm_apply] at hv
      have ho := yonedaEquiv_precomp_operator τ (SimplexCategory.δ l)
      change SSet.yonedaEquiv (SSet.stdSimplex.δ l ≫ τ) = _ at ho
      rw [ho, Equiv.apply_symm_apply]
      change C.map ((ordinalJoinLeft ⦋k⦌).map (SimplexCategory.δ l)).op r = _
      rw [joinMap_coface]
      have hm := yonedaEquiv_precomp_operator μC
        (SimplexCategory.δ (suffixIndex k (n + 1) l))
      exact hm.symm.trans hv
    have hτhorn : φ ≫ (prefixFiber ⦋k⦌ C f).ι = Λ[n + 1, i].ι ≫ τ := by
      apply SSet.horn.hom_ext
      intro l hl
      have heq : SSet.horn.ι i l hl ≫ (φ ≫ (prefixFiber ⦋k⦌ C f).ι) =
          SSet.horn.ι i l hl ≫ (Λ[n + 1, i].ι ≫ τ) := by
        rw [← Category.assoc (SSet.horn.ι i l hl) Λ[n + 1, i].ι τ,
          SSet.horn.ι_ι]
        exact (hτsource l hl).symm
      have hv := congrArg SSet.yonedaEquiv heq
      simpa only [SSet.yonedaEquiv_comp, SSet.horn.yonedaEquiv_ι] using hv
    have hτboundary : τ ≫ joinedBoundaryRestriction k C = βC := by
      apply (SSet.yonedaEquiv (X := boundaryJoinedPresheaf k C)
        (n := ⦋n + 1⦌)).injective
      rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
      change (prefixBoundary k (n + 1)).ι ≫
        (SSet.yonedaEquiv (X := C) (n := ⦋k + (n + 1) + 1⦌)).symm
          ((SSet.yonedaEquiv (X := C) (n := ⦋k + (n + 1) + 1⦌)) μC) = _
      rw [Equiv.symm_apply_apply]
      exact hμboundary
    let j := Fin.last (n + 1)
    have hj : j ≠ i := ne_of_gt hi
    let t := (SSet.yonedaEquiv (X := simplexCoslice ⦋k⦌ C f)
      (n := ⦋n⦌)) (SSet.horn.ι i j hj ≫ φ)
    have hsource : SSet.stdSimplex.δ j ≫ τ =
        (SSet.horn.ι i j hj ≫ φ) ≫ (prefixFiber ⦋k⦌ C f).ι := by
      rw [Category.assoc, hτhorn, ← Category.assoc, SSet.horn.ι_ι]
    have hs : (joinedPresheaf ⦋k⦌ C).map (SimplexCategory.δ j).op r = t.val := by
      have hv := congrArg SSet.yonedaEquiv hsource
      have ho := yonedaEquiv_precomp_operator τ (SimplexCategory.δ j)
      change SSet.yonedaEquiv (SSet.stdSimplex.δ j ≫ τ) = _ at ho
      rw [ho, SSet.yonedaEquiv_comp] at hv
      simpa only [τ, Equiv.apply_symm_apply] using hv
    have hr : r ∈ (prefixFiber ⦋k⦌ C f).obj (op ⦋n + 1⦌) := by
      have hprefix := prefix_operator_eq ⦋k⦌ (SimplexCategory.δ j) r
      rw [hs] at hprefix
      change C.map (AugmentedSimplexCategory.inl' ⦋k⦌ ⦋n + 1⦌).op r = f
      exact hprefix.symm.trans t.property
    let σ : (Δ[n + 1] : SSet.{u}) ⟶ simplexCoslice ⦋k⦌ C f :=
      SSet.yonedaEquiv.symm ⟨r, hr⟩
    have hσ : σ ≫ (prefixFiber ⦋k⦌ C f).ι = τ := by
      apply (SSet.yonedaEquiv (X := joinedPresheaf ⦋k⦌ C) (n := ⦋n + 1⦌)).injective
      rw [SSet.yonedaEquiv_comp]
      change ((SSet.yonedaEquiv (X := simplexCoslice ⦋k⦌ C f) (n := ⦋n + 1⦌))
        ((SSet.yonedaEquiv (X := simplexCoslice ⦋k⦌ C f) (n := ⦋n + 1⦌)).symm
          ⟨r, hr⟩)).val = SSet.yonedaEquiv (SSet.yonedaEquiv.symm r)
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    have hσhorn : φ = Λ[n + 1, i].ι ≫ σ := by
      apply (cancel_mono (prefixFiber ⦋k⦌ C f).ι).mp
      rw [Category.assoc, hσ]
      exact hτhorn
    have hσC : σ ≫ cosliceBoundaryRestriction k C f = βC := by
      change σ ≫ ((prefixFiber ⦋k⦌ C f).ι ≫ joinedBoundaryRestriction k C) = βC
      rw [← Category.assoc, hσ]
      exact hτboundary
    have hσD : σ ≫ cosliceMap p ⦋k⦌ f = βD := by
      apply (SSet.yonedaEquiv (X := simplexCoslice ⦋k⦌ D
        (p.app (op ⦋k⦌) f)) (n := ⦋n + 1⦌)).injective
      rw [SSet.yonedaEquiv_comp]
      apply Subtype.ext
      change p.app (op ⦋k + (n + 1) + 1⦌)
        ((SSet.yonedaEquiv (X := simplexCoslice ⦋k⦌ C f) (n := ⦋n + 1⦌)) σ).val =
          bD.val
      change p.app (op ⦋k + (n + 1) + 1⦌)
        ((SSet.yonedaEquiv (X := simplexCoslice ⦋k⦌ C f) (n := ⦋n + 1⦌))
          ((SSet.yonedaEquiv (X := simplexCoslice ⦋k⦌ C f) (n := ⦋n + 1⦌)).symm
            ⟨r, hr⟩)).val = bD.val
      rw [Equiv.apply_symm_apply]
      change p.app (op ⦋k + (n + 1) + 1⦌) r = bD.val
      have hv := congrArg (SSet.yonedaEquiv (X := D)
        (n := ⦋k + (n + 1) + 1⦌)) hμbase
      rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at hv
      exact hv
    refine CommSq.HasLift.mk' ⟨σ, hσhorn.symm, ?_⟩
    apply pullback.hom_ext
    · simpa only [Category.assoc, relativeCosliceRestriction, pullback.lift_fst] using hσC
    · simpa only [Category.assoc, relativeCosliceRestriction, pullback.lift_snd] using hσD

#print axioms relativeCosliceRestriction_hasLiftingProperty

end

end DaggerOriginalRelativeCosliceRestrictionLifting
