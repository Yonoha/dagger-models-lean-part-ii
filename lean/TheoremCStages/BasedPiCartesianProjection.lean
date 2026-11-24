import CartesianSimplicialMapFibration
import BasedPiOperatorWeakTransfer

/-! Fiberwise bijective based-pi operators make the total based-pi projection cartesian. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite HomotopicalAlgebra
open SSet.KanComplex
open DaggerNativeBasedPiFreeEvaluationPullback DaggerNativeTotalBasedPiFunctor
open DaggerBasedPiOperatorWeakTransfer DaggerCartesianSimplicialMapFibration
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerBasedPiCartesianProjection
noncomputable section

/-- A based-pi operator is fiberwise bijective exactly where the total based-pi map
has a pullback square over its underlying vertex map. -/
theorem basedProjection_naturality_isPullback (F : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    (n : ℕ)
    (hOp : ∀ ⦃k l : SimplexCategoryᵒᵖ⦄ (α : k ⟶ l) (x : (F.obj k) _⦋0⦌),
      Function.Bijective (mapπ (F.map α) n x _ rfl))
    ⦃k l : SimplexCategoryᵒᵖ⦄ (α : k ⟶ l) :
    IsPullback ((basedRows F n).map α) ((basedProjection F n).app k)
      ((basedProjection F n).app l) ((vertexRows F).map α) := by
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨(basedProjection F n).naturality α, ?_, ?_⟩
  · rintro ⟨x, s⟩ ⟨y, t⟩ ⟨he, hv⟩
    change x = y at hv
    subst y
    change (⟨(F.map α).app _ x, mapπ (F.map α) n x _ rfl s⟩ :
      Σ z : (F.obj l) _⦋0⦌, π n (F.obj l) z) =
        ⟨(F.map α).app _ x, mapπ (F.map α) n x _ rfl t⟩ at he
    have hs : s = t := (hOp α x).injective (eq_of_heq (Sigma.mk.inj he).2)
    subst t
    rfl
  · intro z x h
    obtain ⟨y, t⟩ := z
    change y = (F.map α).app _ x at h
    subst y
    obtain ⟨s, hs⟩ := (hOp α x).surjective t
    refine ⟨⟨x, s⟩, ?_, rfl⟩
    exact Sigma.ext rfl (heq_of_eq hs)

/-- The total based-pi projection is a Kan fibration whenever every outer operator
is bijective on every actual based-pi fiber. No Kan assumption is needed here. -/
theorem basedProjection_fibration (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ)
    (hOp : ∀ ⦃k l : SimplexCategoryᵒᵖ⦄ (α : k ⟶ l) (x : (F.obj k) _⦋0⦌),
      Function.Bijective (mapπ (F.map α) n x _ rfl)) :
    Fibration (basedProjection F n) :=
  fibration_of_cartesian_naturality (basedProjection F n)
    (by
      intro k l α
      exact basedProjection_naturality_isPullback F n hOp α)

/-- The same fibration condition transfers forward along a rowwise weak equivalence
of Kan-row diagrams, without any triviality assumption on fundamental-group actions. -/
theorem target_basedProjection_fibration {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}}
    [∀ k, IsFibrant (F.obj k)] [∀ k, IsFibrant (G.obj k)]
    (f : F ⟶ G) (hf : ∀ k, WeakEquivalence (f.app k)) (n : ℕ)
    (hOpF : ∀ ⦃k l : SimplexCategoryᵒᵖ⦄ (α : k ⟶ l) (x : (F.obj k) _⦋0⦌),
      Function.Bijective (mapπ (F.map α) n x _ rfl)) :
    Fibration (basedProjection G n) := by
  apply basedProjection_fibration G n
  intro k l α y
  exact operator_mapπ_bijective f hf n hOpF α y

#print axioms basedProjection_naturality_isPullback
#print axioms basedProjection_fibration
#print axioms target_basedProjection_fibration

end
end DaggerBasedPiCartesianProjection
