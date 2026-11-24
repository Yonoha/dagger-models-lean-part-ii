import DaggerModelsPartII.JTBarChainSSet
import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

/-!
# Vertical degeneracies of the full reversal-index bar

The installed bar has degree `r` data `(c, h, x)` with `c` a full
reversal-index chain, `h : d ⟶ c.left`, and `x : P(op c.right)`.
This module isolates the degeneracy-lifting property needed for the
projective free-cell presentation: a bar simplex is vertically degenerate
exactly when its index chain is degenerate in the nerve of `ReverseSimplex`.
No thinness or omission of reversal automorphisms is assumed.

Projective cofibrancy and diagram-level skeletal pushouts are separate.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.JTBarNondegenerateCells

noncomputable section

open JTProjectiveBar JTBarChains JTBarSimplicialChains

/-- Forget the represented arrow and coefficient, retaining the complete
reversal-index chain. This is a simplicial map because it is a nerve map. -/
def indexProjection (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) : barValue P d ⟶ nerve ReverseSimplex :=
  nerveMap ((StructuredArrow.proj d (elementIndex P)) ⋙ elementIndex P)

/-- The projection agrees with the first component of the checked chain
equivalence, including every reversal morphism. -/
theorem indexProjection_apply (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) (r : ℕ)
    (γ : (barValue P d).obj (op ⦋r⦌)) :
    (indexProjection P d).app (op ⦋r⦌) γ =
      (barDegreeEquiv P d r γ).1 := by
  rfl

/-- A simplex operator collapsing one adjacent pair preserves the first
and terminal reversal indices. -/
private theorem sigma_left (r : ℕ) (i : Fin (r + 1))
    (c : ComposableArrows ReverseSimplex r) :
    ((nerve ReverseSimplex).σ i c).left = c.left := by
  simp [ComposableArrows.left, nerve.σ_obj]

private theorem sigma_right (r : ℕ) (i : Fin (r + 1))
    (c : ComposableArrows ReverseSimplex r) :
    ((nerve ReverseSimplex).σ i c).right = c.right := by
  change c.obj (i.predAbove (Fin.last (r + 1))) = c.obj (Fin.last r)
  rw [Fin.predAbove_right_last]

/-- Type-valued functor transport along an object equality cancels its
inverse transport. -/
private theorem map_eqToHom_symm_transport
    {C : Type*} [Category C] (F : C ⥤ Type)
    {a b : C} (e : a = b) (x : F.obj a) :
    F.map (eqToHom e.symm) (Eq.mp (congrArg F.obj e) x) = x := by
  cases e
  simp

/-- A degeneracy of the index chain lifts through the represented arrow
and coefficient data. The lower chain uses the same endpoint data. -/
theorem chain_sigma_lift (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) (r : ℕ) (i : Fin (r + 1))
    (a : ChainData P d (r + 1))
    (c : ComposableArrows ReverseSimplex r)
    (hc : a.1 = (nerve ReverseSimplex).σ i c) :
    ∃ a' : ChainData P d r,
      chainSimplexMap P d (SimplexCategory.σ i) a' = a := by
  rcases a with ⟨c₀, h, x⟩
  change c₀ = (nerve ReverseSimplex).σ i c at hc
  subst c₀
  let hl := sigma_left r i c
  let hr := sigma_right r i c
  let h' : d ⟶ c.left := h ≫ eqToHom hl
  let x' : P.obj (op c.right) :=
    Eq.mp (congrArg (fun t => P.obj (op t)) hr) x
  refine ⟨⟨c, h', x'⟩, ?_⟩
  apply Sigma.ext
  · rfl
  · simp [chainSimplexMap, thetaIndex, h', x']
    constructor
    · exact Category.comp_id h
    · let j := (thetaIndex (SimplexCategory.σ i)).obj (Fin.last (r + 1))
      have ej : j = Fin.last r := by
        change i.predAbove (Fin.last (r + 1)) = Fin.last r
        exact Fin.predAbove_right_last
      have hf : homOfLE (Fin.le_last j) = eqToHom ej :=
        Subsingleton.elim _ _
      rw [hf, eqToHom_map, eqToHom_op]
      simpa only [x'] using
        map_eqToHom_symm_transport P (congrArg op hr) x

/-- The bar simplex is in the image of a fixed degeneracy exactly when
its full index chain is in the image of that degeneracy. -/
theorem bar_sigma_range_iff_index_sigma_range
    (P : ReverseSimplexᵒᵖ ⥤ Type) (d : ReverseSimplex)
    (r : ℕ) (i : Fin (r + 1))
    (γ : (barValue P d).obj (op ⦋r + 1⦌)) :
    γ ∈ Set.range ((barValue P d).σ i) ↔
      (indexProjection P d).app (op ⦋r + 1⦌) γ ∈
        Set.range ((nerve ReverseSimplex).σ i) := by
  constructor
  · rintro ⟨γ', rfl⟩
    refine ⟨(indexProjection P d).app (op ⦋r⦌) γ', ?_⟩
    exact SSet.σ_naturality_apply (indexProjection P d) i γ'
  · rintro ⟨c, hc⟩
    let a := barDegreeEquiv P d (r + 1) γ
    have hca : a.1 = (nerve ReverseSimplex).σ i c := by
      simpa only [a, indexProjection_apply] using hc.symm
    obtain ⟨a', ha'⟩ := chain_sigma_lift P d r i a c hca
    refine ⟨(barDegreeEquiv P d r).symm a', ?_⟩
    apply (barDegreeEquiv P d (r + 1)).injective
    change barDegreeEquiv P d (r + 1)
      ((barValue P d).map (SimplexCategory.σ i).op
        ((barDegreeEquiv P d r).symm a')) = _
    rw [barDegreeEquiv_natural]
    simpa only [Equiv.apply_symm_apply, a] using ha'

/-- Degeneracy depends only on the complete index chain; the represented
arrow and terminal coefficient carry no additional degeneracy obstruction. -/
theorem bar_degenerate_iff_index_degenerate
    (P : ReverseSimplexᵒᵖ ⥤ Type) (d : ReverseSimplex)
    (r : ℕ) (γ : (barValue P d).obj (op ⦋r⦌)) :
    γ ∈ (barValue P d).degenerate r ↔
      (indexProjection P d).app (op ⦋r⦌) γ ∈
        (nerve ReverseSimplex).degenerate r := by
  cases r with
  | zero => simp
  | succ r =>
      simp only [SSet.degenerate_eq_iUnion_range_σ, Set.mem_iUnion]
      exact exists_congr (fun i => bar_sigma_range_iff_index_sigma_range P d r i γ)

/-- The equivalent nondegeneracy criterion is now a property of the full
index chain alone. -/
theorem bar_nonDegenerate_iff_index_nonDegenerate
    (P : ReverseSimplexᵒᵖ ⥤ Type) (d : ReverseSimplex)
    (r : ℕ) (γ : (barValue P d).obj (op ⦋r⦌)) :
    γ ∈ (barValue P d).nonDegenerate r ↔
      (barDegreeEquiv P d r γ).1 ∈
        (nerve ReverseSimplex).nonDegenerate r := by
  rw [SSet.mem_nonDegenerate_iff_notMem_degenerate,
    SSet.mem_nonDegenerate_iff_notMem_degenerate,
    ← indexProjection_apply]
  exact not_congr (bar_degenerate_iff_index_degenerate P d r γ)


/-- A cell label is a nondegenerate full reversal-index chain together
with its terminal coefficient. Its first vertex determines the free outer
representable. -/
def NondegenerateLabel (P : ReverseSimplexᵒᵖ ⥤ Type)
    (r : ℕ) : Type :=
  Σ c : (nerve ReverseSimplex).nonDegenerate r,
    P.obj (op c.1.right)

/-- The pointwise coproduct of outer representables indexed by the
nondegenerate full chains and terminal coefficients. -/
def freeNondegenerateValue (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) (r : ℕ) : Type :=
  Σ t : NondegenerateLabel P r, d ⟶ t.1.1.left

/-- Repacking chain data as a free outer cell respects equality of the
full chain data; the nondegeneracy witnesses are proof-irrelevant. -/
private theorem freeNondegenerate_repack_congr
    (P : ReverseSimplexᵒᵖ ⥤ Type) (d : ReverseSimplex) (r : ℕ)
    {a b : ChainData P d r} (e : a = b)
    (ha : a.1 ∈ (nerve ReverseSimplex).nonDegenerate r)
    (hb : b.1 ∈ (nerve ReverseSimplex).nonDegenerate r) :
    (⟨⟨⟨a.1, ha⟩, a.2.2⟩, a.2.1⟩ : freeNondegenerateValue P d r) =
      ⟨⟨⟨b.1, hb⟩, b.2.2⟩, b.2.1⟩ := by
  cases e
  rfl

/-- The free-representable presentation of degree-`r` nondegenerate bar
simplices. This equivalence retains every reversal morphism and automorphism. -/
def freeNondegenerateEquiv (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) (r : ℕ) :
    freeNondegenerateValue P d r ≃ (barValue P d).nonDegenerate r where
  toFun z :=
    ⟨(barDegreeEquiv P d r).symm ⟨z.1.1.1, z.2, z.1.2⟩,
      (bar_nonDegenerate_iff_index_nonDegenerate P d r _).2 (by
        simpa only [Equiv.apply_symm_apply] using z.1.1.2)⟩
  invFun γ :=
    let a := barDegreeEquiv P d r γ.1
    ⟨⟨⟨a.1,
        (bar_nonDegenerate_iff_index_nonDegenerate P d r γ.1).1 γ.2⟩,
        a.2.2⟩,
      a.2.1⟩
  left_inv z := by
    rcases z with ⟨⟨⟨c, hc⟩, x⟩, h⟩
    have ha : barDegreeEquiv P d r
        ((barDegreeEquiv P d r).symm ⟨c, (h, x)⟩) =
        ⟨c, (h, x)⟩ := (barDegreeEquiv P d r).apply_symm_apply _
    dsimp only
    exact freeNondegenerate_repack_congr P d r ha _ _
  right_inv γ := by
    apply Subtype.ext
    simp

/-- Outer reversal action on the free-representable presentation is
precomposition of the represented first arrow; the label stays fixed. -/
def freeNondegenerateOuterMap (P : ReverseSimplexᵒᵖ ⥤ Type)
    {d e : ReverseSimplex} (f : d ⟶ e) (r : ℕ) :
    freeNondegenerateValue P e r → freeNondegenerateValue P d r :=
  fun z => ⟨z.1, f ≫ z.2⟩

/-- The installed outer bar map matches the free-representable action on
nondegenerate cells. -/
theorem freeNondegenerateEquiv_outer (P : ReverseSimplexᵒᵖ ⥤ Type)
    {d e : ReverseSimplex} (f : d ⟶ e) (r : ℕ)
    (z : freeNondegenerateValue P e r) :
    (freeNondegenerateEquiv P d r
      (freeNondegenerateOuterMap P f r z)).1 =
      (barOuterMap P f).app (op ⦋r⦌)
        (freeNondegenerateEquiv P e r z).1 := by
  apply (barDegreeEquiv P d r).injective
  change barDegreeEquiv P d r
      ((barDegreeEquiv P d r).symm
        ⟨z.1.1.1, (f ≫ z.2, z.1.2)⟩) =
    barDegreeEquiv P d r
      ((barOuterMap P f).app (op ⦋r⦌)
        ((barDegreeEquiv P e r).symm
          ⟨z.1.1.1, (z.2, z.1.2)⟩))
  rw [(barDegreeEquiv P d r).apply_symm_apply]
  have ha : barDegreeEquiv P e r
      ((barDegreeEquiv P e r).symm
        ⟨z.1.1.1, z.2, z.1.2⟩) =
      ⟨z.1.1.1, z.2, z.1.2⟩ := (barDegreeEquiv P e r).apply_symm_apply _
  change ⟨z.1.1.1, (f ≫ z.2, z.1.2)⟩ =
    extract P d r
      (((StructuredArrow.map f).mapComposableArrows r).obj
        ((barDegreeEquiv P e r).symm
          ⟨z.1.1.1, (z.2, z.1.2)⟩))
  rw [extract_outer]
  change ⟨z.1.1.1, (f ≫ z.2, z.1.2)⟩ =
    chainOuterMap P f r
      (barDegreeEquiv P e r
        ((barDegreeEquiv P e r).symm
          ⟨z.1.1.1, (z.2, z.1.2)⟩))
  rw [ha]
  rfl

end

end DaggerModels.PartII.JTBarNondegenerateCells
