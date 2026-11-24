import NativeBasedPiWeakPullback
import TopCatModelCategory.SSet.KanComplexW

/-! Rowwise weak equivalences transfer based-pi bijectivity of every outer operator. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite HomotopicalAlgebra
open SSet.KanComplex SSet.KanComplex.FundamentalGroupoid
open DaggerNativeBasedPiWeakPullback
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerBasedPiOperatorWeakTransfer
noncomputable section

variable {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}}
  [∀ k, IsFibrant (F.obj k)] [∀ k, IsFibrant (G.obj k)]

/-- At vertices in the image of a rowwise weak map, operator bijectivity transfers by
the naturality square and cancellation of two based-pi bijections. -/
theorem operator_mapπ_bijective_at_image (f : F ⟶ G)
    (hf : ∀ k, WeakEquivalence (f.app k)) (n : ℕ)
    (hF : ∀ ⦃k l : SimplexCategoryᵒᵖ⦄ (α : k ⟶ l) (x : (F.obj k) _⦋0⦌),
      Function.Bijective (mapπ (F.map α) n x _ rfl))
    ⦃k l : SimplexCategoryᵒᵖ⦄ (α : k ⟶ l) (x : (F.obj k) _⦋0⦌) :
    Function.Bijective (mapπ (G.map α) n ((f.app k).app _ x) _ rfl) := by
  have hleft : Function.Bijective (mapπ (F.map α ≫ f.app l) n x _ rfl) := by
    change Function.Bijective (mapπ (F.map α ≫ f.app l) n x
      ((f.app l).app _ ((F.map α).app _ x)) rfl)
    rw [← mapπ_comp_mapπ (F.map α) n x _ rfl (f.app l) _ rfl]
    exact (based_mapπ_bijective (f.app l) (hf l) n _).comp (hF α x)
  have hright : Function.Bijective (mapπ (f.app k ≫ G.map α) n x _ rfl) := by
    rw [← f.naturality α]
    exact hleft
  rw [← Function.Bijective.of_comp_iff _
    (based_mapπ_bijective (f.app k) (hf k) n x),
    mapπ_comp_mapπ (f.app k) n x _ rfl (G.map α) _ rfl]
  exact hright

/-- A rowwise weak equivalence transports the operator condition to every actual target
vertex. Fundamental-groupoid path transport handles vertices outside the literal image. -/
theorem operator_mapπ_bijective (f : F ⟶ G)
    (hf : ∀ k, WeakEquivalence (f.app k)) (n : ℕ)
    (hF : ∀ ⦃k l : SimplexCategoryᵒᵖ⦄ (α : k ⟶ l) (x : (F.obj k) _⦋0⦌),
      Function.Bijective (mapπ (F.map α) n x _ rfl))
    ⦃k l : SimplexCategoryᵒᵖ⦄ (α : k ⟶ l) (y : (G.obj k) _⦋0⦌) :
    Function.Bijective (mapπ (G.map α) n y _ rfl) := by
  have hw : W (f.app k) := (SSet.weakEquivalence_iff_kanComplexW _).mp (hf k)
  have : (mapFundamentalGroupoid (f.app k)).IsEquivalence := hw.isEquivalence
  let z := (mapFundamentalGroupoid (f.app k)).objPreimage (FundamentalGroupoid.mk y)
  let e := (mapFundamentalGroupoid (f.app k)).objObjPreimageIso
    (FundamentalGroupoid.mk y)
  exact W.bijective_of_iso (f := G.map α) e
    (operator_mapπ_bijective_at_image f hf n hF α z.pt)

#print axioms operator_mapπ_bijective_at_image
#print axioms operator_mapπ_bijective

end
end DaggerBasedPiOperatorWeakTransfer
