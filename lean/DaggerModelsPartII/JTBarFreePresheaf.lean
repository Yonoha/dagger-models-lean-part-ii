import DaggerModelsPartII.JTBarNondegenerateCells
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.CategoryTheory.Limits.Presheaf

/-!
# The free outer presheaf of nondegenerate bar cells

For a fixed vertical degree, the nondegenerate full reversal-index chains
and terminal coefficients label a categorical coproduct of `uliftYoneda`
representables. The explicit cell equivalence is natural in the outer
reversal index and identifies this coproduct with the actual nondegenerate
bar simplices. This is the free-cell input for a later projective skeletal
attachment argument; no projective cofibrancy is asserted here.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.JTBarFreePresheaf

noncomputable section

open JTProjectiveBar JTBarChains JTBarNondegenerateCells

/-- The pointwise free presentation assembled into an outer presheaf. -/
def freeOuterPresheaf (P : ReverseSimplexᵒᵖ ⥤ Type) (r : ℕ) :
    ReverseSimplexᵒᵖ ⥤ Type where
  obj d := freeNondegenerateValue P d.unop r
  map {d e} f := freeNondegenerateOuterMap P f.unop r
  map_id d := by
    funext z
    rcases z with ⟨t, h⟩
    simp [freeNondegenerateOuterMap]
  map_comp f g := by
    funext z
    rcases z with ⟨t, h⟩
    simp [freeNondegenerateOuterMap, Category.assoc, unop_comp]

/-- The actual degree-`r` nondegenerate bar simplices as an outer presheaf. -/
def barNondegeneratePresheaf (P : ReverseSimplexᵒᵖ ⥤ Type) (r : ℕ) :
    ReverseSimplexᵒᵖ ⥤ Type where
  obj d := (barValue P d.unop).nonDegenerate r
  map {d e} f := fun z =>
    ⟨(barOuterMap P f.unop).app (op ⦋r⦌) z.1, by
      apply (bar_nonDegenerate_iff_index_nonDegenerate P e.unop r _).2
      have hz := (bar_nonDegenerate_iff_index_nonDegenerate P d.unop r z.1).1 z.2
      change (extract P e.unop r
        (((StructuredArrow.map f.unop).mapComposableArrows r).obj z.1)).1 ∈
          (nerve ReverseSimplex).nonDegenerate r
      rw [extract_outer]
      exact hz⟩
  map_id d := by
    funext z
    apply Subtype.ext
    change ((barPresheaf P).map (𝟙 d)).app (op ⦋r⦌) z.1 = z.1
    rw [(barPresheaf P).map_id]
    rfl
  map_comp f g := by
    funext z
    apply Subtype.ext
    change ((barPresheaf P).map (f ≫ g)).app (op ⦋r⦌) z.1 =
      ((barPresheaf P).map g).app (op ⦋r⦌)
        (((barPresheaf P).map f).app (op ⦋r⦌) z.1)
    rw [(barPresheaf P).map_comp]
    rfl

/-- The checked pointwise chain equivalence is natural in every outer
reversal morphism. -/
def freeOuterIsoBarNondegenerate (P : ReverseSimplexᵒᵖ ⥤ Type) (r : ℕ) :
    freeOuterPresheaf P r ≅ barNondegeneratePresheaf P r :=
  NatIso.ofComponents (fun d => (freeNondegenerateEquiv P d.unop r).toIso) (by
    intro d e f
    funext z
    apply Subtype.ext
    exact freeNondegenerateEquiv_outer P f.unop r z)

/-- One `uliftYoneda` summand maps to its free cell at every outer index. -/
def freeSummand (P : ReverseSimplexᵒᵖ ⥤ Type) (r : ℕ)
    (t : NondegenerateLabel P r) :
    uliftYoneda.{0}.obj t.1.1.left ⟶ freeOuterPresheaf P r where
  app d u := ⟨t, u.down⟩
  naturality := by
    intro d e f
    funext u
    rfl

/-- The named categorical coproduct of representable outer presheaves. -/
def freeRepresentableCoproduct (P : ReverseSimplexᵒᵖ ⥤ Type) (r : ℕ) :
    ReverseSimplexᵒᵖ ⥤ Type :=
  ∐ (fun t : NondegenerateLabel P r => uliftYoneda.{0}.obj t.1.1.left)

/-- The coproduct map given by the generating free cells. -/
def coproductToFree (P : ReverseSimplexᵒᵖ ⥤ Type) (r : ℕ) :
    freeRepresentableCoproduct P r ⟶ freeOuterPresheaf P r :=
  Sigma.desc (fun t => freeSummand P r t)

/-- Its inverse inserts a labelled represented arrow in the corresponding
categorical coproduct summand. -/
def freeToCoproduct (P : ReverseSimplexᵒᵖ ⥤ Type) (r : ℕ) :
    freeOuterPresheaf P r ⟶ freeRepresentableCoproduct P r where
  app d z :=
    (Sigma.ι (fun t : NondegenerateLabel P r =>
      uliftYoneda.{0}.obj t.1.1.left) z.1).app d (ULift.up z.2)
  naturality := by
    intro d e f
    funext z
    rcases z with ⟨t, h⟩
    exact congrFun ((Sigma.ι (fun t : NondegenerateLabel P r =>
      uliftYoneda.{0}.obj t.1.1.left) t).naturality f) (ULift.up h)

/-- The actual coproduct of `uliftYoneda` representables is the free outer
presheaf, with the stated generating inclusion. -/
def coproductIsoFree (P : ReverseSimplexᵒᵖ ⥤ Type) (r : ℕ) :
    freeRepresentableCoproduct P r ≅ freeOuterPresheaf P r where
  hom := coproductToFree P r
  inv := freeToCoproduct P r
  hom_inv_id := by
    apply Sigma.hom_ext
    intro t
    change (Sigma.ι (fun t : NondegenerateLabel P r =>
      uliftYoneda.{0}.obj t.1.1.left) t ≫
        Sigma.desc (fun t => freeSummand P r t)) ≫
      freeToCoproduct P r =
      Sigma.ι (fun t : NondegenerateLabel P r =>
        uliftYoneda.{0}.obj t.1.1.left) t
    rw [Sigma.ι_desc]
    apply NatTrans.ext
    funext d u
    cases u
    rfl
  inv_hom_id := by
    apply NatTrans.ext
    funext d z
    rcases z with ⟨t, h⟩
    have hh := Sigma.ι_desc (fun t : NondegenerateLabel P r =>
      freeSummand P r t) t
    exact congrFun (congrArg (fun η => η.app d) hh) (ULift.up h)

/-- Degree-`r` nondegenerate bar cells are a named categorical coproduct
of represented outer presheaves, naturally in the outer index. -/
def coproductIsoBarNondegenerate
    (P : ReverseSimplexᵒᵖ ⥤ Type) (r : ℕ) :
    freeRepresentableCoproduct P r ≅ barNondegeneratePresheaf P r :=
  coproductIsoFree P r ≪≫ freeOuterIsoBarNondegenerate P r

end

end DaggerModels.PartII.JTBarFreePresheaf
