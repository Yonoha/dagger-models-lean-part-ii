import DaggerModelsPartII.JTBarChains

/-!
# Simplicial operators on the explicit bar chains

For an arbitrary map of finite ordinals `θ : ⦋p⦌ ⟶ ⦋r⦌`, precomposition
of a bar nerve simplex with `θ` has a literal action on the degreewise chain
presentation. The index chain is precomposed with `θ`; the first represented
simplex is advanced to `θ(0)`; the terminal coefficient is pulled back from
`r` to `θ(p)`. This retains every reversal-index morphism.

The statement is about the vertical simplicial structure of the installed
bar rows. It does not assert projective cofibrancy, a coend comparison, or a
derived density map.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.JTBarSimplicialChains

noncomputable section

open JTProjectiveBar JTBarChains

/-- The functor on ordinal indices underlying an arbitrary simplex map. -/
def thetaIndex {p r : ℕ} (θ : ⦋p⦌ ⟶ ⦋r⦌) :
    Fin (p + 1) ⥤ Fin (r + 1) :=
  (SimplexCategory.toCat.map θ).toFunctor

/-- An arbitrary simplex operator on the literal bar-chain data. The
first represented simplex and terminal coefficient follow the two endpoint
changes, with no restriction on the reversal-index chain. -/
def chainSimplexMap (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) {p r : ℕ} (θ : ⦋p⦌ ⟶ ⦋r⦌) :
    ChainData P d r → ChainData P d p :=
  fun a =>
    ⟨a.1.whiskerLeft (thetaIndex θ),
      a.2.1 ≫ a.1.map
        (homOfLE (Fin.zero_le ((thetaIndex θ).obj 0))),
      P.map (a.1.map
        (homOfLE (Fin.le_last ((thetaIndex θ).obj (Fin.last p))))).op
        a.2.2⟩

/-- On every degree and for every simplex operator, extraction commutes
with the native nerve's precomposition. -/
theorem extract_simplex (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) {p r : ℕ} (θ : ⦋p⦌ ⟶ ⦋r⦌)
    (γ : ComposableArrows (barCategory P d) r) :
    extract P d p ((barValue P d).map θ.op γ) =
      chainSimplexMap P d θ (extract P d r γ) := by
  apply Sigma.ext
  · apply CategoryTheory.Functor.ext
    case h_obj =>
      intro i
      rfl
    case h_map =>
      intro i j f
      rfl
  · simp [extract, chainSimplexMap, thetaIndex,
      ComposableArrows.whiskerLeft]
    constructor
    · rfl
    · exact (γ.map (homOfLE
        (Fin.le_last ((thetaIndex θ).obj (Fin.last p))))).right.unop.property.symm

/-- The installed degreewise equivalence is compatible with every vertical
simplex operator, including all face and degeneracy maps. -/
theorem barDegreeEquiv_natural (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) {p r : ℕ} (θ : ⦋p⦌ ⟶ ⦋r⦌)
    (γ : (barValue P d).obj (op ⦋r⦌)) :
    barDegreeEquiv P d p ((barValue P d).map θ.op γ) =
      chainSimplexMap P d θ (barDegreeEquiv P d r γ) :=
  extract_simplex P d θ γ

end

end DaggerModels.PartII.JTBarSimplicialChains
