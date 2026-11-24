import SimplicialSetLocalSystem
import NativeSimplexPullbackFibrationDetection
import ActualConstantSimplicialCategory

/-!
# Fibration of a set-valued local system over any category nerve

Every simplex pullback of the local-system projection is a product with
the constant simplicial set of values at the simplex's initial object.
The inverse uses bijectivity of transport along the initial arrow.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite Simplicial
open HomotopicalAlgebra DaggerUnitaryDiscrete
open DaggerNativeSimplexPullbackFibrationDetection
open DaggerNativeOverNerveSimplexFamily (restrictChain)
open DaggerNativeSimplicialReplacementCells (initialArrow)
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.SimplicialSetLocalSystemFibration

open SimplicialSetLocalSystem

noncomputable section

variable {C : Type u} [Category.{u} C] (L : C ⥤ Type u)
variable (hL : ∀ ⦃a b : C⦄ (f : a ⟶ b), Function.Bijective (L.map f))

/-- Over a fixed base simplex, transport a value at its first object
to the first object of each restricted chain. -/
def simplexFamily {n : ℕ} (A : Fin (n + 1) ⥤ C) :
    (Δ[n] : SSet.{u}) ⊗ constSSet (L.obj (A.obj 0)) ⟶ localSystem L where
  app q p := ⟨restrictChain A p.1, L.map (firstArrow A p.1) p.2⟩
  naturality q r α := by
    funext p
    rcases p with ⟨t, x⟩
    change
      (⟨restrictChain A ((Δ[n] : SSet.{u}).map α t),
        L.map (firstArrow A ((Δ[n] : SSet.{u}).map α t)) x⟩ :
          (localSystem L).obj r) =
        ⟨(nerve C).map α (restrictChain A t),
          L.map (initialArrow α (restrictChain A t))
            (L.map (firstArrow A t) x)⟩
    rw [firstArrow_comp, L.map_comp]
    rfl

/-- The family forgets to the exact original base simplex. -/
theorem simplexFamily_projection {n : ℕ} (A : Fin (n + 1) ⥤ C) :
    simplexFamily L A ≫ projection L =
      fst (Δ[n] : SSet.{u}) (constSSet (L.obj (A.obj 0))) ≫
        SSet.yonedaEquiv.symm A := by
  apply NatTrans.ext
  funext q p
  rfl

include hL

/-- In every vertical degree, bijective initial transport gives the
universal property of the literal simplex pullback. -/
theorem simplexFamily_app_isPullback {n : ℕ} (A : Fin (n + 1) ⥤ C)
    (q : SimplexCategoryᵒᵖ) :
    IsPullback ((simplexFamily L A).app q)
      ((fst (Δ[n] : SSet.{u}) (constSSet (L.obj (A.obj 0)))).app q)
      ((projection L).app q) ((SSet.yonedaEquiv.symm A).app q) := by
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨NatTrans.congr_app (simplexFamily_projection L A) q, ?_, ?_⟩
  · rintro ⟨t, x⟩ ⟨s, y⟩ ⟨hf, ht⟩
    change t = s at ht
    subst s
    apply Prod.ext
    · rfl
    · exact (hL (firstArrow A t)).injective (eq_of_heq (Sigma.mk.inj hf).2)
  · intro B t h
    rcases B with ⟨c, z⟩
    change c = restrictChain A t at h
    subst c
    obtain ⟨x, hx⟩ := (hL (firstArrow A t)).surjective z
    refine ⟨(t, x), ?_, rfl⟩
    change (⟨restrictChain A t, L.map (firstArrow A t) x⟩ :
      (localSystem L).obj q) = ⟨restrictChain A t, z⟩
    rw [hx]

/-- The entire fixed-simplex family is the strict pullback of the
local-system projection, without assuming the base is a groupoid. -/
theorem simplexFamily_isPullback {n : ℕ} (A : Fin (n + 1) ⥤ C) :
    IsPullback (simplexFamily L A)
      (fst (Δ[n] : SSet.{u}) (constSSet (L.obj (A.obj 0))))
      (projection L) (SSet.yonedaEquiv.symm A) := by
  let c := PullbackCone.mk (simplexFamily L A)
    (fst (Δ[n] : SSet.{u}) (constSSet (L.obj (A.obj 0))))
    (simplexFamily_projection L A)
  apply IsPullback.of_isLimit (c := c)
  apply evaluationJointlyReflectsLimits
  intro q
  let h := simplexFamily_app_isPullback L hL A q
  refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_ h.isLimit
  · exact cospanIsoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · refine Cones.ext (Iso.refl _) ?_
    rintro (_ | _ | _) <;> rfl

def simplexPullbackIso {n : ℕ} (A : Fin (n + 1) ⥤ C) :
    (Δ[n] : SSet.{u}) ⊗ constSSet (L.obj (A.obj 0)) ≅
      pullback (projection L)
        ((SSet.yonedaEquiv (X := nerve C) (n := ⦋n⦌)).symm A) :=
  (simplexFamily_isPullback L hL A).isoPullback

/-- A local system with bijective transport is a Kan fibration over the
nerve of any category. -/
theorem projection_fibration : Fibration (projection L) := by
  apply fibration_of_simplex_pullbacks
  intro n b
  let A : Fin (n + 1) ⥤ C := SSet.yonedaEquiv b
  have hb : SSet.yonedaEquiv.symm A = b := SSet.yonedaEquiv.symm_apply_apply b
  rw [← hb]
  have : (constSSet (L.obj (A.obj 0))).KanComplex := constSSet_fibrant _
  have : Fibration (fst (Δ[n] : SSet.{u}) (constSSet (L.obj (A.obj 0)))) :=
    product_projection_fibration _ _
  let e := simplexPullbackIso L hL A
  let a : Arrow.mk (fst (Δ[n] : SSet.{u}) (constSSet (L.obj (A.obj 0)))) ≅
      Arrow.mk (pullback.snd (projection L)
        ((SSet.yonedaEquiv (X := nerve C) (n := ⦋n⦌)).symm A)) :=
    Arrow.isoMk e (Iso.refl _) (by
      exact (simplexFamily_isPullback L hL A).isoPullback_hom_snd)
  apply (HomotopicalAlgebra.fibration_iff _).mpr
  exact ((fibrations SSet.{u}).arrow_mk_iso_iff a).mp
    ((HomotopicalAlgebra.fibration_iff _).mp inferInstance)

#print axioms simplexFamily_isPullback
#print axioms projection_fibration

end
end DaggerModels.PartII.SimplicialSetLocalSystemFibration
