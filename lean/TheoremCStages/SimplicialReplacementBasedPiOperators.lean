import SimplicialReplacementBasedPi
import NativeFamilyLoopAction

/-!
# Positive based homotopy groups of replacement operators

Every original horizontal replacement operator acts bijectively on
positive based homotopy groups when the original value maps are weak
equivalences between Kan simplicial sets.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Simplicial Opposite HomotopicalAlgebra
open SSet.KanComplex
open DaggerNativeSimplicialReplacementCells (first initialArrow family)
open DaggerOriginalProductGadget (familyInclusion)
open DaggerSSetFamilyBasedPi (familyPiEquiv familyPiEquiv_apply)
open DaggerNativeTotalBasedPiFunctor (totalPiFunctor)
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.SimplicialReplacementBasedPiOperators

noncomputable section

variable {C : Type u} [Category.{u} C] (G : C ⥤ SSet.{u})
variable [∀ a, IsFibrant (G.obj a)] (n : ℕ)

private instance familyValueFibrant (q : SimplexCategoryᵒᵖ) :
    ∀ c : (nerve C).obj q, IsFibrant ((family G q) c) :=
  fun c ↦ show IsFibrant (G.obj (first c)) from inferInstance

/-- Each complete original replacement row is Kan under the given
pointwise Kan hypothesis. -/
instance replacementRowFibrant (q : SimplexCategoryᵒᵖ) :
    IsFibrant ((DaggerNativeSimplicialReplacement.replacement G).obj q) := by
  change IsFibrant (DaggerOriginalProductGadget.familySSet (family G q))
  infer_instance

omit [∀ a, IsFibrant (G.obj a)] in
private theorem inclusion_horizontal {q r : SimplexCategoryᵒᵖ}
    (α : q ⟶ r) (c : (nerve C).obj q) :
    familyInclusion (family G q) c ≫
        (DaggerNativeSimplicialReplacement.replacement G).map α =
      G.map (initialArrow α c) ≫
        familyInclusion (family G r) ((nerve C).map α c) := by
  apply NatTrans.ext
  rfl

/-- The operator action on a class in one original summand is exactly
the original value map, conjugated by the two summand equivalences. -/
theorem operator_mapπ_square {q r : SimplexCategoryᵒᵖ}
    (α : q ⟶ r) (c : (nerve C).obj q)
    (x : (G.obj (first c)) _⦋0⦌)
    (s : π (n + 1) (G.obj (first c)) x) :
    mapπ ((DaggerNativeSimplicialReplacement.replacement G).map α)
        (n + 1) ⟨c, x⟩
        ⟨(nerve C).map α c, (G.map (initialArrow α c)).app _ x⟩ rfl
        (familyPiEquiv (family G q) c x n s) =
      familyPiEquiv (family G r) ((nerve C).map α c)
        ((G.map (initialArrow α c)).app _ x) n
        (mapπ (G.map (initialArrow α c)) (n + 1) x _ rfl s) := by
  have h :
      (totalPiFunctor (n + 1)).map
          ((DaggerNativeSimplicialReplacement.replacement G).map α)
          ((totalPiFunctor (n + 1)).map (familyInclusion (family G q) c)
            ⟨x, s⟩) =
        (totalPiFunctor (n + 1)).map
          (familyInclusion (family G r) ((nerve C).map α c))
          ((totalPiFunctor (n + 1)).map (G.map (initialArrow α c))
            ⟨x, s⟩) := by
    calc
      _ = (totalPiFunctor (n + 1)).map
          (familyInclusion (family G q) c ≫
            (DaggerNativeSimplicialReplacement.replacement G).map α)
            ⟨x, s⟩ := by
              rw [(totalPiFunctor (n + 1)).map_comp]
              rfl
      _ = (totalPiFunctor (n + 1)).map
          (G.map (initialArrow α c) ≫
            familyInclusion (family G r) ((nerve C).map α c))
            ⟨x, s⟩ := by rw [inclusion_horizontal]
      _ = _ := by
        rw [(totalPiFunctor (n + 1)).map_comp]
        rfl
  change (⟨_, mapπ ((DaggerNativeSimplicialReplacement.replacement G).map α)
      (n + 1) ⟨c, x⟩ _ rfl
      (mapπ (familyInclusion (family G q) c) (n + 1) x _ rfl s)⟩ :
        (totalPiFunctor (n + 1)).obj
          ((DaggerNativeSimplicialReplacement.replacement G).obj r)) =
    ⟨_, mapπ (familyInclusion (family G r) ((nerve C).map α c))
      (n + 1) _ _ rfl
      (mapπ (G.map (initialArrow α c)) (n + 1) x _ rfl s)⟩ at h
  rw [familyPiEquiv_apply, familyPiEquiv_apply]
  exact eq_of_heq (Sigma.mk.inj h).2

/-- Every original horizontal operator is bijective on positive based
homotopy groups at every original vertex and every positive index. -/
theorem operator_mapπ_bijective
    (hG : ∀ ⦃a b : C⦄ (f : a ⟶ b), WeakEquivalence (G.map f))
    {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r)
    (c : (nerve C).obj q) (x : (G.obj (first c)) _⦋0⦌) :
    Function.Bijective
      (mapπ ((DaggerNativeSimplicialReplacement.replacement G).map α)
        (n + 1) ⟨c, x⟩
        ⟨(nerve C).map α c, (G.map (initialArrow α c)).app _ x⟩ rfl) := by
  let e₀ := familyPiEquiv (family G q) c x n
  let e₁ := familyPiEquiv (family G r) ((nerve C).map α c)
    ((G.map (initialArrow α c)).app _ x) n
  have h := DaggerNativeBasedPiWeakPullback.based_mapπ_bijective
    (G.map (initialArrow α c)) (hG (initialArrow α c)) (n + 1) x
  constructor
  · intro v w hvw
    obtain ⟨s, rfl⟩ := e₀.surjective v
    obtain ⟨t, rfl⟩ := e₀.surjective w
    rw [operator_mapπ_square G n α c x s,
      operator_mapπ_square G n α c x t] at hvw
    exact congrArg e₀ (h.injective (e₁.injective hvw))
  · intro w
    obtain ⟨t, ht⟩ := e₁.surjective w
    obtain ⟨s, hs⟩ := h.surjective t
    refine ⟨e₀ s, ?_⟩
    rw [operator_mapπ_square G n α c x s, hs, ht]

/-- The same bijectivity statement for an arbitrary literal vertex of
the original replacement row. -/
theorem operator_mapπ_bijective_at
    (hG : ∀ ⦃a b : C⦄ (f : a ⟶ b), WeakEquivalence (G.map f))
    {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r)
    (z : ((DaggerNativeSimplicialReplacement.replacement G).obj q) _⦋0⦌) :
    Function.Bijective
      (mapπ ((DaggerNativeSimplicialReplacement.replacement G).map α)
        (n + 1) z _ rfl) := by
  rcases z with ⟨c, x⟩
  exact operator_mapπ_bijective G n hG α c x

#print axioms replacementRowFibrant
#print axioms operator_mapπ_square
#print axioms operator_mapπ_bijective
#print axioms operator_mapπ_bijective_at

end
end DaggerModels.PartII.SimplicialReplacementBasedPiOperators
