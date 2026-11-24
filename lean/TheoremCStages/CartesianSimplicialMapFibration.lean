import NativeOverGroupoidNerveFibration
import TopCatModelCategory.SSet.NonDegenerateProdSimplex

/-! A simplicial map with pullback naturality squares is a Kan fibration. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite Simplicial
open HomotopicalAlgebra DaggerUnitaryDiscrete
open DaggerNativeSimplexPullbackFibrationDetection
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerCartesianSimplicialMapFibration
noncomputable section

variable {E B : SSet.{u}} (p : E ⟶ B)

/-- The fiber of `p` over the whole chosen top-dimensional base simplex. -/
def simplexFiber {n : ℕ} (b : (Δ[n] : SSet.{u}) ⟶ B) : Type u :=
  {e : E _⦋n⦌ // p.app _ e = SSet.yonedaEquiv b}

/-- Restrict a simplex in the top fiber along an arbitrary simplex operator. -/
def simplexFamily {n : ℕ} (b : (Δ[n] : SSet.{u}) ⟶ B) :
    (Δ[n] : SSet.{u}) ⊗ constSSet (simplexFiber p b) ⟶ E where
  app v z := (SSet.yonedaEquiv.symm z.2.val).app v z.1
  naturality v w α := by
    funext z
    change (SSet.yonedaEquiv.symm z.2.val).app w ((Δ[n] : SSet.{u}).map α z.1) =
      E.map α ((SSet.yonedaEquiv.symm z.2.val).app v z.1)
    exact congrFun ((SSet.yonedaEquiv.symm z.2.val).naturality α) z.1

theorem simplexFamily_projection {n : ℕ} (b : (Δ[n] : SSet.{u}) ⟶ B) :
    simplexFamily p b ≫ p = fst (Δ[n] : SSet.{u}) (constSSet (simplexFiber p b)) ≫ b := by
  apply NatTrans.ext
  funext v z
  change p.app v ((SSet.yonedaEquiv.symm z.2.val).app v z.1) = b.app v z.1
  have h : SSet.yonedaEquiv.symm z.2.val ≫ p = b := by
    rw [SSet.yonedaEquiv_symm_comp, z.2.property]
    exact SSet.yonedaEquiv.symm_apply_apply b
  exact congrFun (NatTrans.congr_app h v) z.1

variable (hcart : ∀ ⦃v w : SimplexCategoryᵒᵖ⦄ (α : v ⟶ w),
  IsPullback (E.map α) (p.app v) (p.app w) (B.map α))

include hcart

theorem simplexFamily_app_isPullback {n : ℕ} (b : (Δ[n] : SSet.{u}) ⟶ B)
    (v : SimplexCategoryᵒᵖ) :
    IsPullback ((simplexFamily p b).app v)
      ((fst (Δ[n] : SSet.{u}) (constSSet (simplexFiber p b))).app v)
      (p.app v) (b.app v) := by
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨NatTrans.congr_app (simplexFamily_projection p b) v, ?_, ?_⟩
  · rintro ⟨t, e⟩ ⟨s, e'⟩ ⟨he, ht⟩
    change t = s at ht
    subst s
    change E.map (SSet.stdSimplex.objEquiv t).op e.val =
      E.map (SSet.stdSimplex.objEquiv t).op e'.val at he
    have hc := (Types.isPullback_iff _ _ _ _).mp
      (hcart (SSet.stdSimplex.objEquiv t).op)
    have hv : e.val = e'.val := hc.2.1 e.val e'.val
      ⟨he, by rw [e.property, e'.property]⟩
    have : e = e' := Subtype.ext hv
    subst e'
    rfl
  · intro a t ht
    have hb : b.app v t = B.map (SSet.stdSimplex.objEquiv t).op
        (SSet.yonedaEquiv b) := by
      calc
        b.app v t = (SSet.yonedaEquiv.symm (SSet.yonedaEquiv b)).app v t := by
          rw [SSet.yonedaEquiv.symm_apply_apply]
        _ = _ := SSet.yonedaEquiv_symm_app_apply _ _
    have hc : p.app v a = B.map (SSet.stdSimplex.objEquiv t).op
        (SSet.yonedaEquiv b) := ht.trans hb
    have hp := (Types.isPullback_iff _ _ _ _).mp
      (hcart (SSet.stdSimplex.objEquiv t).op)
    obtain ⟨e, he, hpe⟩ := hp.2.2 a (SSet.yonedaEquiv b) hc
    refine ⟨(t, ⟨e, hpe⟩), ?_, rfl⟩
    change E.map (SSet.stdSimplex.objEquiv t).op e = a
    exact he

theorem simplexFamily_isPullback {n : ℕ} (b : (Δ[n] : SSet.{u}) ⟶ B) :
    IsPullback (simplexFamily p b)
      (fst (Δ[n] : SSet.{u}) (constSSet (simplexFiber p b))) p b := by
  let c := PullbackCone.mk (simplexFamily p b)
    (fst (Δ[n] : SSet.{u}) (constSSet (simplexFiber p b)))
    (simplexFamily_projection p b)
  apply IsPullback.of_isLimit (c := c)
  apply evaluationJointlyReflectsLimits
  intro v
  let h := simplexFamily_app_isPullback p hcart b v
  refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_ h.isLimit
  · exact cospanIsoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · refine Cones.ext (Iso.refl _) ?_
    rintro (_ | _ | _) <;> rfl

/-- All simplicial-operator pullback squares make `p` a Kan fibration, with no Kan
assumption on either its source or target. -/
theorem fibration_of_cartesian_naturality : Fibration p := by
  apply fibration_of_simplex_pullbacks
  intro n b
  have : (constSSet (simplexFiber p b)).KanComplex := constSSet_fibrant _
  have : Fibration (fst (Δ[n] : SSet.{u}) (constSSet (simplexFiber p b))) :=
    product_projection_fibration _ _
  let e := (simplexFamily_isPullback p hcart b).isoPullback
  let a : Arrow.mk (fst (Δ[n] : SSet.{u}) (constSSet (simplexFiber p b))) ≅
      Arrow.mk (pullback.snd p b) :=
    Arrow.isoMk e (Iso.refl _) (by
      exact (simplexFamily_isPullback p hcart b).isoPullback_hom_snd)
  apply (HomotopicalAlgebra.fibration_iff _).mpr
  exact ((fibrations SSet.{u}).arrow_mk_iso_iff a).mp
    ((HomotopicalAlgebra.fibration_iff _).mp inferInstance)

#print axioms simplexFamily_isPullback
#print axioms fibration_of_cartesian_naturality

end
end DaggerCartesianSimplicialMapFibration
