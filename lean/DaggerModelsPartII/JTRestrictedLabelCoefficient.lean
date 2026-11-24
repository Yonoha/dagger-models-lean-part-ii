import DaggerModelsPartII.JTNecklaceLabelRealization
import ChosenNecklaceBeadMaps
import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

/-!
# Nondegenerate coefficients of restricted JT labels

On any horizontal restriction of a decorated label, the actual raw
realization reads only its nondegenerate coefficient. Equality after the
resulting simplex operator suffices for equality of the complete graphs.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open CartesianMonoidalCategory DaggerModels

namespace DaggerModels.PartII.JTRestrictedLabelCoefficient

open JTNecklaceLabelRealization (realizedLabel realizedLabel_natural_X realizedLabel_natural_k)
open ReversalDiscreteFreeColimits (discreteFree)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev J := GroupoidSimplex.parameter
private abbrev F := discreteFree.{0}
private abbrev Label (W : Source) (X : SSet.{0}) := diagramMappingSpace (F.obj X) W

variable {W : Source} {X Y : SSet.{0}} {k : SimplexCategory}
variable (i : X ⟶ Y) (η : (Label W Y).obj (op k))

private abbrev restriction : (Label W X).obj (op k) :=
  Functor.whiskerRight (F.map i) (tensorRight (SSet.stdSimplex.obj k)) ≫ η

/-- A nondegenerate factor of the actual horizontally restricted label. -/
structure Factor where
  degree : ℕ
  operator : k ⟶ ⦋degree⦌
  epi : Epi operator
  simplex : (Label W X).nonDegenerate degree
  equation : restriction i η = (Label W X).map operator.op simplex.val

private theorem exists_core {A : SSet.{0}} {m : SimplexCategory} (a : A.obj (op m)) :
    ∃ (n : ℕ) (f : m ⟶ ⦋n⦌) (_ : Epi f) (c : A.nonDegenerate n),
      a = A.map f.op c.val := by
  induction m using SimplexCategory.rec with
  | h n => exact A.exists_nonDegenerate a

/-- Mathlib's degeneracy decomposition provides the factor for any source restriction. -/
theorem nonempty_factor : Nonempty (Factor i η) := by
  obtain ⟨m, r, hr, ξ, hξ⟩ := exists_core (restriction i η)
  exact ⟨⟨m, r, hr, ξ, hξ⟩⟩

/-- Use the nondegenerate simplex and the actual ordinal operator of the restriction. -/
def factor : Factor i η := Classical.choice (nonempty_factor i η)

variable (D : Factor i η)

/-- The actual realized label on the horizontal restriction factors through
the groupoid completion of its nondegenerate coefficient operator. -/
theorem Factor.realized :
    (i ⊗ₘ 𝟙 (J.obj k)) ≫ realizedLabel Y W k η =
      (𝟙 X ⊗ₘ J.map D.operator) ≫ realizedLabel X W ⦋D.degree⦌ D.simplex.val := by
  rw [realizedLabel_natural_X, realizedLabel_natural_k]
  exact congrArg (realizedLabel X W k) D.equation

/-- On the full graph with horizontal map factoring through the given
restriction, equality of the projected coefficients implies equality of its raw maps. -/
theorem Factor.graph_eq {A : SSet.{0}} (h : A ⟶ X) (s t : A ⟶ J.obj k)
    (e : s ≫ J.map D.operator = t ≫ J.map D.operator) :
    lift (h ≫ i) s ≫ realizedLabel Y W k η =
      lift (h ≫ i) t ≫ realizedLabel Y W k η := by
  have hg (p : A ⟶ J.obj k) :
      lift (h ≫ i) p ≫ realizedLabel Y W k η =
        lift h (p ≫ J.map D.operator) ≫ realizedLabel X W ⦋D.degree⦌ D.simplex.val := by
    have h' := (lift_map h p i (𝟙 (J.obj k))).symm
    rw [Category.comp_id] at h'
    rw [h', Category.assoc, D.realized, ← Category.assoc, lift_map, Category.comp_id]
  rw [hg s, hg t, e]

set_option maxHeartbeats 600000 in
/-- If the restricted label is already pulled back by a given coefficient map,
its nondegenerate operator identifies every pair identified by that map.
The given coefficient map may be non-surjective. -/
theorem Factor.operator_eq_of_map {m : SimplexCategory} (r : k ⟶ m)
    (a : (Label W X).obj (op m))
    (h : restriction i η = (Label W X).map r.op a)
    {u v : Fin (k.len + 1)} (e : r.toOrderHom u = r.toOrderHom v) :
    D.operator.toOrderHom u = D.operator.toOrderHom v := by
  let f := factorThruImage r
  let g := image.ι r
  let A := Label W X
  let z := A.map g.op a
  obtain ⟨n, c, hc, b, hb⟩ := exists_core z
  letI : Epi c := hc
  have hr : restriction i η = A.map (f ≫ c).op b.val := by
    calc
      _ = A.map r.op a := h
      _ = A.map (f ≫ g).op a :=
        congrArg (fun q : k ⟶ m ↦ A.map q.op a) (image.fac r).symm
      _ = A.map f.op z := by
        rw [op_comp, A.map_comp, CategoryTheory.types_comp_apply]
      _ = A.map (f ≫ c).op b.val := by
        rw [op_comp, A.map_comp, CategoryTheory.types_comp_apply, ← hb]
  have hfg : ((f ≫ g).toOrderHom u) = ((f ≫ g).toOrderHom v) := by
    exact (SimplexCategory.congr_toOrderHom_apply (image.fac r) u).trans
      (e.trans (SimplexCategory.congr_toOrderHom_apply (image.fac r) v).symm)
  have hg : Function.Injective g.toOrderHom := SimplexCategory.mono_iff_injective.mp inferInstance
  have hf : f.toOrderHom u = f.toOrderHom v := hg hfg
  have hfc : (f ≫ c).toOrderHom u = (f ≫ c).toOrderHom v :=
    congrArg c.toOrderHom hf
  obtain ⟨d, t, ht, y, hy⟩ := D
  letI : Epi t := ht
  change t.toOrderHom u = t.toOrderHom v
  induction k using SimplexCategory.rec with
  | h k =>
    have hdim := A.unique_nonDegenerate_dim _ t y hy (f ≫ c) b hr
    subst n
    have ht' := A.unique_nonDegenerate_map _ t y hy (f ≫ c) b hr
    rw [ht']
    exact hfc

open DaggerChosenRigidificationNecklace

/-- Every simplex in the whole product lies in a point or bead piece with
the same original time simplex. -/
theorem bead_product_cover (T : NecklaceCode) {I : SSet.{0}}
    {q : SimplexCategoryᵒᵖ} (z : (T.toSSet ⊗ I).obj q) :
    ∃ (b : Option T.Bead) (v : ((T.pieces b).toSSet ⊗ I).obj q),
      (T.pieceι b ⊗ₘ 𝟙 I).app q v = z := by
  induction q using Opposite.rec with
  | op q =>
    induction q using SimplexCategory.rec with
    | h n =>
      let x : T.toSSet.obj (op ⦋n⦌) := z.1
      obtain ⟨b, a, ha⟩ := T.simplex_factors_piece (SSet.yonedaEquiv.symm x)
      have hx : (T.pieceι b).app (op ⦋n⦌) (SSet.yonedaEquiv a) = x := by
        rw [← SSet.yonedaEquiv_comp, ha, Equiv.apply_symm_apply]
      exact ⟨b, (SSet.yonedaEquiv a, z.2), Prod.ext hx rfl⟩

/-- The actual point and bead pieces, multiplied by all time simplices,
jointly detect equality. This includes the zero-length necklace. -/
theorem bead_product_hom_ext (T : NecklaceCode) {I Z : SSet.{0}}
    {f g : T.toSSet ⊗ I ⟶ Z}
    (h : ∀ b : Option T.Bead, (T.pieceι b ⊗ₘ 𝟙 I) ≫ f = (T.pieceι b ⊗ₘ 𝟙 I) ≫ g) :
    f = g := by
  apply NatTrans.ext
  funext q z
  induction q using Opposite.rec with
  | op q =>
    induction q using SimplexCategory.rec with
    | h n =>
      let x : T.toSSet.obj (op ⦋n⦌) := z.1
      obtain ⟨b, a, ha⟩ := T.simplex_factors_piece (SSet.yonedaEquiv.symm x)
      have hx : (T.pieceι b).app (op ⦋n⦌) (SSet.yonedaEquiv a) = x := by
        rw [← SSet.yonedaEquiv_comp, ha, Equiv.apply_symm_apply]
      have hz := congrFun (NatTrans.congr_app (h b) (op ⦋n⦌))
        (SSet.yonedaEquiv a, z.2)
      change f.app (op ⦋n⦌) ((T.pieceι b).app (op ⦋n⦌) (SSet.yonedaEquiv a), z.2) =
        g.app (op ⦋n⦌) ((T.pieceι b).app (op ⦋n⦌) (SSet.yonedaEquiv a), z.2) at hz
      rw [hx] at hz
      exact hz

end

end DaggerModels.PartII.JTRestrictedLabelCoefficient
