import DaggerModelsPartII.JTBarSimplicialChains

/-!
# The explicit bar-chain simplicial set

The literal chain data form a simplicial set under the arbitrary simplex
operators proved in `JTBarSimplicialChains`. Its functor laws follow by
transporting the installed bar nerve laws through the already proved
surjective degreewise equivalence. The degreewise equivalences then assemble
into an actual isomorphism of simplicial sets.

This is a simplicial-set comparison only. No coend realization,
projective-cofibrancy, or derived-density assertion is made here.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.JTBarChainSSet

noncomputable section

open JTProjectiveBar JTBarChains JTBarSimplicialChains

/-- The literal chain presentation as an actual simplicial set. -/
def chainSSet (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) : SSet.{0} where
  obj n := ChainData P d n.unop.len
  map {n m} θ := chainSimplexMap P d θ.unop
  map_id n := by
    funext a
    obtain ⟨γ, rfl⟩ := (barDegreeEquiv P d n.unop.len).surjective a
    change chainSimplexMap P d (𝟙 ⦋n.unop.len⦌)
      (barDegreeEquiv P d n.unop.len γ) =
        barDegreeEquiv P d n.unop.len γ
    rw [← barDegreeEquiv_natural P d (𝟙 ⦋n.unop.len⦌) γ]
    simp
  map_comp {n m k} θ ψ := by
    induction n using Opposite.rec with | op n =>
      induction n using SimplexCategory.rec with | h n =>
        induction m using Opposite.rec with | op m =>
          induction m using SimplexCategory.rec with | h m =>
            induction k using Opposite.rec with | op k =>
              induction k using SimplexCategory.rec with | h k =>
                funext a
                obtain ⟨γ, rfl⟩ := (barDegreeEquiv P d n).surjective a
                change chainSimplexMap P d (ψ.unop ≫ θ.unop)
                    (barDegreeEquiv P d n γ) =
                  chainSimplexMap P d ψ.unop
                    (chainSimplexMap P d θ.unop
                      (barDegreeEquiv P d n γ))
                calc
                  chainSimplexMap P d (ψ.unop ≫ θ.unop)
                      (barDegreeEquiv P d n γ) =
                      barDegreeEquiv P d k
                        ((barValue P d).map (θ ≫ ψ) γ) := by
                          simpa only [unop_comp, op_comp] using
                            (barDegreeEquiv_natural P d (ψ.unop ≫ θ.unop) γ).symm
                  _ = barDegreeEquiv P d k
                      ((barValue P d).map ψ ((barValue P d).map θ γ)) := by
                        rw [Functor.map_comp]
                        rfl
                  _ = chainSimplexMap P d ψ.unop
                      (barDegreeEquiv P d m
                        ((barValue P d).map θ γ)) :=
                          barDegreeEquiv_natural P d ψ.unop _
                  _ = chainSimplexMap P d ψ.unop
                      (chainSimplexMap P d θ.unop
                        (barDegreeEquiv P d n γ)) := by
                          exact congrArg (chainSimplexMap P d ψ.unop)
                            (barDegreeEquiv_natural P d θ.unop γ)

/-- The full simplicial-set isomorphism whose component is the checked
literal chain equivalence at every degree. -/
def barValueChainIso (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) : barValue P d ≅ chainSSet P d :=
  NatIso.ofComponents
    (fun n => (barDegreeEquiv P d n.unop.len).toIso) (by
      intro n m θ
      induction n using Opposite.rec with | op n =>
        induction n using SimplexCategory.rec with | h n =>
          induction m using Opposite.rec with | op m =>
            induction m using SimplexCategory.rec with | h m =>
              funext γ
              exact barDegreeEquiv_natural P d θ.unop γ)

/-- At each simplex degree, the outer reversal-index map changes only the
first represented arrow in the explicit chain coordinates. -/
theorem barValueChainIso_outer (P : ReverseSimplexᵒᵖ ⥤ Type)
    {d e : ReverseSimplex} (f : d ⟶ e)
    (n : SimplexCategoryᵒᵖ) (γ : (barValue P e).obj n) :
    (barValueChainIso P d).hom.app n
      ((barOuterMap P f).app n γ) =
      chainOuterMap P f n.unop.len
        ((barValueChainIso P e).hom.app n γ) :=
  extract_outer P f n.unop.len γ

/-- At each simplex degree, a coefficient map changes only the terminal
presheaf element in the explicit chain coordinates. -/
theorem barValueChainIso_coefficient
    {P Q : ReverseSimplexᵒᵖ ⥤ Type} (α : P ⟶ Q)
    (d : ReverseSimplex) (n : SimplexCategoryᵒᵖ)
    (γ : (barValue P d).obj n) :
    (barValueChainIso Q d).hom.app n
      ((barWeightMap α d).app n γ) =
      chainCoefficientMap α d n.unop.len
        ((barValueChainIso P d).hom.app n γ) :=
  extract_coefficient α d n.unop.len γ

end

end DaggerModels.PartII.JTBarChainSSet
