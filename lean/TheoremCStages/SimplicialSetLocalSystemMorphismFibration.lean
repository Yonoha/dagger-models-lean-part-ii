import SimplicialSetLocalSystem
import NativeSimplexPullbackFibrationDetection
import ActualConstantSimplicialCategory

/-!
# Relative fibration of set-valued local systems

A natural transformation of local systems is a Kan fibration when each
transport between its set-theoretic fibers is bijective. Neither the
source nor target local system is required to have bijective transport.
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

namespace DaggerModels.PartII.SimplicialSetLocalSystemMorphismFibration

open SimplicialSetLocalSystem

noncomputable section

variable {C : Type u} [Category.{u} C]
variable {U V : C ⥤ Type u} (φ : U ⟶ V)

/-- Apply the original component transformation to the value at each
chain's initial object while retaining the whole base chain. -/
def mapSystem : localSystem U ⟶ localSystem V where
  app q := fun z ↦ ⟨z.1, φ.app (DaggerNativeSimplicialReplacementCells.first z.1) z.2⟩
  naturality q r α := by
    funext z
    rcases z with ⟨c, x⟩
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      change φ.app (DaggerNativeSimplicialReplacementCells.first
          ((nerve C).map α c)) (U.map (initialArrow α c) x) =
        V.map (initialArrow α c)
          (φ.app (DaggerNativeSimplicialReplacementCells.first c) x)
      exact congrFun (φ.naturality (initialArrow α c)) x

/-- The strict fiber at one value of the target local system. -/
def fiber (a : C) (y : V.obj a) : Type u :=
  {x : U.obj a // φ.app a x = y}

/-- The actual transport between strict set-theoretic fibers. -/
def fiberTransport {a b : C} (f : a ⟶ b) (y : V.obj a) :
    fiber φ a y → fiber φ b (V.map f y) :=
  fun x ↦ ⟨U.map f x.val, by
    have h := congrFun (φ.naturality f) x.val
    change φ.app b (U.map f x.val) = V.map f (φ.app a x.val) at h
    rw [x.property] at h
    exact h⟩

variable (hφ : ∀ ⦃a b : C⦄ (f : a ⟶ b) (y : V.obj a),
  Function.Bijective (fiberTransport φ f y))

/-- Over one target simplex, choose the strict fiber at its initial value
and transport each element to every restricted first vertex. -/
def simplexFamily {n : ℕ} (A : Fin (n + 1) ⥤ C) (y₀ : V.obj (A.obj 0)) :
    (Δ[n] : SSet.{u}) ⊗ constSSet (fiber φ (A.obj 0) y₀) ⟶ localSystem U where
  app q p := ⟨restrictChain A p.1, U.map (firstArrow A p.1) p.2.val⟩
  naturality q r α := by
    funext p
    rcases p with ⟨t, x⟩
    change
      (⟨restrictChain A ((Δ[n] : SSet.{u}).map α t),
        U.map (firstArrow A ((Δ[n] : SSet.{u}).map α t)) x.val⟩ :
          (localSystem U).obj r) =
        ⟨(nerve C).map α (restrictChain A t),
          U.map (initialArrow α (restrictChain A t))
            (U.map (firstArrow A t) x.val)⟩
    rw [firstArrow_comp, U.map_comp]
    rfl

/-- The target simplex whose first value is `y₀`, with all later
values induced by the original functor `V`. -/
def targetSimplex {n : ℕ} (A : Fin (n + 1) ⥤ C)
    (y₀ : V.obj (A.obj 0)) :
    (Δ[n] : SSet.{u}) ⟶ localSystem V :=
  SSet.yonedaEquiv.symm (⟨A, y₀⟩ : (localSystem V).obj (op ⦋n⦌))

/-- The family projects to exactly the chosen target simplex. -/
theorem simplexFamily_target {n : ℕ} (A : Fin (n + 1) ⥤ C)
    (y₀ : V.obj (A.obj 0)) :
    simplexFamily φ A y₀ ≫ mapSystem φ =
      fst (Δ[n] : SSet.{u}) (constSSet (fiber φ (A.obj 0) y₀)) ≫
        targetSimplex (V := V) A y₀ := by
  apply NatTrans.ext
  funext q p
  rcases p with ⟨t, x⟩
  change
    (⟨restrictChain A t,
      φ.app _ (U.map (firstArrow A t) x.val)⟩ :
        (localSystem V).obj q) =
      ⟨restrictChain A t, V.map (firstArrow A t) y₀⟩
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    have h := congrFun (φ.naturality (firstArrow A t)) x.val
    change φ.app _ (U.map (firstArrow A t) x.val) =
      V.map (firstArrow A t) (φ.app _ x.val) at h
    rw [x.property] at h
    exact h

include hφ

/-- Each degree of the target-simplex family is the exact pullback;
surjectivity uses bijective transport on the specified fiber. -/
theorem simplexFamily_app_isPullback {n : ℕ} (A : Fin (n + 1) ⥤ C)
    (y₀ : V.obj (A.obj 0)) (q : SimplexCategoryᵒᵖ) :
    IsPullback ((simplexFamily φ A y₀).app q)
      ((fst (Δ[n] : SSet.{u}) (constSSet (fiber φ (A.obj 0) y₀))).app q)
      ((mapSystem φ).app q) ((targetSimplex (V := V) A y₀).app q) := by
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨NatTrans.congr_app (simplexFamily_target φ A y₀) q, ?_, ?_⟩
  · rintro ⟨t, x⟩ ⟨s, y⟩ ⟨hf, ht⟩
    change t = s at ht
    subst s
    apply Prod.ext
    · rfl
    · apply (hφ (firstArrow A t) y₀).injective
      apply Subtype.ext
      exact eq_of_heq (Sigma.mk.inj hf).2
  · intro B t h
    rcases B with ⟨c, z⟩
    have hc : c = restrictChain A t := (Sigma.mk.inj h).1
    subst c
    have hz : φ.app _ z = V.map (firstArrow A t) y₀ :=
      eq_of_heq (Sigma.mk.inj h).2
    let zf : fiber φ (DaggerNativeSimplicialReplacementCells.first
        (restrictChain A t)) (V.map (firstArrow A t) y₀) := ⟨z, hz⟩
    obtain ⟨x, hx⟩ := (hφ (firstArrow A t) y₀).surjective zf
    refine ⟨(t, x), ?_, rfl⟩
    change (⟨restrictChain A t, U.map (firstArrow A t) x.val⟩ :
      (localSystem U).obj q) = ⟨restrictChain A t, z⟩
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      exact congrArg Subtype.val hx

/-- The entire chosen simplex family is the strict pullback of the
actual map between local systems. -/
theorem simplexFamily_isPullback {n : ℕ} (A : Fin (n + 1) ⥤ C)
    (y₀ : V.obj (A.obj 0)) :
    IsPullback (simplexFamily φ A y₀)
      (fst (Δ[n] : SSet.{u}) (constSSet (fiber φ (A.obj 0) y₀)))
      (mapSystem φ) (targetSimplex (V := V) A y₀) := by
  let c := PullbackCone.mk (simplexFamily φ A y₀)
    (fst (Δ[n] : SSet.{u}) (constSSet (fiber φ (A.obj 0) y₀)))
    (simplexFamily_target φ A y₀)
  apply IsPullback.of_isLimit (c := c)
  apply evaluationJointlyReflectsLimits
  intro q
  let h := simplexFamily_app_isPullback φ hφ A y₀ q
  refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_ h.isLimit
  · exact cospanIsoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · refine Cones.ext (Iso.refl _) ?_
    rintro (_ | _ | _) <;> rfl

def simplexPullbackIso {n : ℕ} (A : Fin (n + 1) ⥤ C)
    (y₀ : V.obj (A.obj 0)) :
    (Δ[n] : SSet.{u}) ⊗ constSSet (fiber φ (A.obj 0) y₀) ≅
      pullback (mapSystem φ) (targetSimplex (V := V) A y₀) :=
  (simplexFamily_isPullback φ hφ A y₀).isoPullback

/-- Bijective transport on every strict fiber makes the complete
local-system morphism a Kan fibration over any base category. -/
theorem mapSystem_fibration : Fibration (mapSystem φ) := by
  apply fibration_of_simplex_pullbacks
  intro n b
  let z : (localSystem V).obj (op ⦋n⦌) := SSet.yonedaEquiv b
  let A : Fin (n + 1) ⥤ C := z.1
  let y₀ : V.obj (A.obj 0) := z.2
  have hb : targetSimplex (V := V) A y₀ = b := SSet.yonedaEquiv.symm_apply_apply b
  rw [← hb]
  have : (constSSet (fiber φ (A.obj 0) y₀)).KanComplex := constSSet_fibrant _
  have : Fibration (fst (Δ[n] : SSet.{u})
      (constSSet (fiber φ (A.obj 0) y₀))) := product_projection_fibration _ _
  let e := simplexPullbackIso φ hφ A y₀
  let a : Arrow.mk (fst (Δ[n] : SSet.{u})
        (constSSet (fiber φ (A.obj 0) y₀))) ≅
      Arrow.mk (pullback.snd (mapSystem φ) (targetSimplex (V := V) A y₀)) :=
    Arrow.isoMk e (Iso.refl _) (by
      exact (simplexFamily_isPullback φ hφ A y₀).isoPullback_hom_snd)
  apply (HomotopicalAlgebra.fibration_iff _).mpr
  exact ((fibrations SSet.{u}).arrow_mk_iso_iff a).mp
    ((HomotopicalAlgebra.fibration_iff _).mp inferInstance)

#print axioms mapSystem
#print axioms fiberTransport
#print axioms simplexFamily_isPullback
#print axioms mapSystem_fibration

end
end DaggerModels.PartII.SimplicialSetLocalSystemMorphismFibration
