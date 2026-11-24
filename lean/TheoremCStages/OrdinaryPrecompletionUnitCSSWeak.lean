import OrdinaryCSSHorizontalWeak
import OrdinaryCoherentCotensorEvaluationReflection
import OrdinarySegalVerticalPrecompletion

/-!
# CSS weakness of the corrected precompletion unit

At a fixed vertical simplex, the corrected unit is the constant section
for the original groupoid-simplex parameter at that same index. Evaluation
at an actual parameter vertex is Joyal weak on the horizontal quasicategory
row. Its strict section is therefore Joyal weak. The checked horizontal
comparison transfers these rowwise weak equivalences to the original CSS
weak class. No completeness assumption is made on the source.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra MonoidalClosed
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryPrecompletionUnitCSSWeak

open OrdinaryCSSLocalization (Space)
open OrdinarySegalHorizontalCotensorPoint (constantSection)
open OrdinarySegalCotensorPointEvaluation (evaluation constantSection_evaluation)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev flip :=
  flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type 0)
private abbrev JoyalWeak :=
  OrdinaryJTProjectiveQuillen.joyalModel.categoryWithWeakEquivalences.weakEquivalences
private abbrev CategoricalWeak :=
  DaggerNativeJoyalMappingTest.weakCategoricalEquivalences

private theorem categorical_to_joyal {X Y : SSet.{0}} (f : X ⟶ Y)
    (hf : CategoricalWeak f) : JoyalWeak f := by
  have he := DaggerNativeOriginalJoyalSmithModelData.modelData.modelWeak
  change JoyalWeak = CategoricalWeak at he
  rw [he]
  exact hf

private theorem joyal_to_categorical {X Y : SSet.{0}} (f : X ⟶ Y)
    (hf : JoyalWeak f) : CategoricalWeak f := by
  have he := DaggerNativeOriginalJoyalSmithModelData.modelData.modelWeak
  change JoyalWeak = CategoricalWeak at he
  exact he ▸ hf

/-- Evaluation of a horizontal cotensor at its original parameter vertex
is Joyal weak on each literal vertical row of a fibrant Segal space. -/
theorem evaluation_row_joyalWeak_at (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (k : SimplexCategory) (j : Fin (k.len + 1))
    (q : SimplexCategoryᵒᵖ) :
    JoyalWeak ((flip.map
      (evaluation (GroupoidSimplex.parameter.obj k) W
        (JTParameterContraction.parameterVertex k j))).app q) := by
  let K : SSet.{0} := GroupoidSimplex.parameter.obj k
  let v : (Δ[0] : SSet.{0}) ⟶ K :=
    JTParameterContraction.parameterVertex k j
  let X : SSet.{0} := W.flip.obj q
  let A : (OrdinarySegalHorizontalCotensor.cotensor K W).flip.obj q ≅
      (ihom K).obj X := OrdinarySegalCotensorMappingIso.rowIso K W q
  let B : (ihom (Δ[0] : SSet.{0})).obj X ≅ X :=
    OrdinaryCoherentCotensorEvaluationReflection.pointRowIso W q
  let p : (ihom K).obj X ⟶
      (ihom (Δ[0] : SSet.{0})).obj X := (MonoidalClosed.pre v).app X
  haveI : SSet.Quasicategory X := by
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, op ⦋m⦌ = q :=
      ⟨q.unop.len, congrArg op (SimplexCategory.ext _ _ rfl)⟩
    exact OrdinaryCoherentArrowVertexRecognition.horizontalRow_quasicategory
      W hSegal m
  haveI : Mono v := JTParameterVertexKan.vertex_mono k j
  have hv : DaggerNativeJoyalMappingTest.weakCategoricalEquivalences v :=
    OrdinaryJTRightNerveCompleteness.parameterVertex_categorical_weak k j
  have hp : trivialFibrations SSet.{0} p :=
    DaggerNativeWeakMonoWholeRestriction.restriction_Kan_trivial v hv X
  have hpC : CategoricalWeak p :=
    (DaggerNativeJoyalFirstFactorization.kan_trivial_le_candidate_trivial p hp).2
  have hs := OrdinaryCoherentCotensorEvaluationReflection.evaluation_row_square
    W k j q
  change A.hom ≫ p ≫ B.hom =
    (flip.map (evaluation K W v)).app q at hs
  let e : Arrow.mk ((flip.map (evaluation K W v)).app q) ≅ Arrow.mk p :=
    Arrow.isoMk A B.symm (by
      symm
      calc
        (flip.map (evaluation K W v)).app q ≫ B.inv =
            (A.hom ≫ p ≫ B.hom) ≫ B.inv := by rw [hs]
        _ = A.hom ≫ p := by simp only [Category.assoc, Iso.hom_inv_id,
          Category.comp_id])
  exact categorical_to_joyal _
    ((CategoricalWeak.arrow_mk_iso_iff e).mpr hpC)

/-- The same evaluation at the selected vertex of the original parameter
indexed by the actual vertical simplex. -/
theorem evaluation_row_joyalWeak (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (q : SimplexCategoryᵒᵖ) :
    JoyalWeak ((flip.map
      (evaluation (GroupoidSimplex.parameter.obj q.unop) W
        (JTParameterContraction.parameterVertex q.unop
          (0 : Fin (q.unop.len + 1))))).app q) :=
  evaluation_row_joyalWeak_at W hSegal q.unop 0 q

/-- The original constant section is Joyal weak in every horizontal row
at the same outer parameter index. -/
theorem constantSection_row_joyalWeak (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (q : SimplexCategoryᵒᵖ) :
    JoyalWeak (NatTrans.flipApp
      (constantSection (GroupoidSimplex.parameter.obj q.unop) W) q) := by
  let K := GroupoidSimplex.parameter.obj q.unop
  let v := JTParameterContraction.parameterVertex q.unop
    (0 : Fin (q.unop.len + 1))
  let s := NatTrans.flipApp (constantSection K W) q
  let e := NatTrans.flipApp (evaluation K W v) q
  have he : JoyalWeak e := by
    exact evaluation_row_joyalWeak W hSegal q
  have hs : s ≫ e = 𝟙 (W.flip.obj q) := by
    have h := congrArg (fun g : W ⟶ W ↦ NatTrans.flipApp g q)
      (constantSection_evaluation K W v)
    change s ≫ e = 𝟙 (W.flip.obj q) at h
    exact h
  have heC : CategoricalWeak e := joyal_to_categorical e he
  have hcomp : CategoricalWeak (s ≫ e) := by
    rw [hs]
    exact CategoricalWeak.id_mem _
  exact categorical_to_joyal s
    (CategoricalWeak.of_postcomp s e heC hcomp)

/-- The actual corrected precompletion unit is weak in every original
horizontal Joyal row. -/
theorem unit_row_joyalWeak (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (q : SimplexCategoryᵒᵖ) :
    JoyalWeak (NatTrans.flipApp
      (OrdinarySegalVerticalPrecompletion.unit W) q) := by
  have h : NatTrans.flipApp (OrdinarySegalVerticalPrecompletion.unit W) q =
      NatTrans.flipApp
        (constantSection (GroupoidSimplex.parameter.obj q.unop) W) q := by
    apply NatTrans.ext
    funext n
    exact OrdinarySegalVerticalPrecompletion.unit_app_app W n q
  rw [h]
  exact constantSection_row_joyalWeak W hSegal q

/-- The corrected precompletion unit is weak in the fixed ordinary CSS
localization for every injectively fibrant Segal source. -/
theorem unit_cssWeak (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) :
    OrdinaryCSSLocalization.model.categoryWithWeakEquivalences.weakEquivalences
      (OrdinarySegalVerticalPrecompletion.unit W) := by
  apply OrdinaryCSSHorizontalWeak.weak_of_rows
  intro k
  exact unit_row_joyalWeak W hSegal (op k)

/-- The same literal unit is monic as a whole map of ordinary simplicial
spaces, without a fibrancy or Segal assumption. -/
theorem unit_mono (W : Space) :
    Mono (OrdinarySegalVerticalPrecompletion.unit W) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [NatTrans.mono_iff_mono_app]
  intro q
  let K := GroupoidSimplex.parameter.obj q.unop
  let v := JTParameterContraction.parameterVertex q.unop
    (0 : Fin (q.unop.len + 1))
  have hs : ((OrdinarySegalVerticalPrecompletion.unit W).app n).app q ≫
      ((evaluation K W v).app n).app q = 𝟙 _ := by
    rw [OrdinarySegalVerticalPrecompletion.unit_app_app]
    have h := congrArg (fun g : W ⟶ W ↦ (g.app n).app q)
      (constantSection_evaluation K W v)
    simpa only [NatTrans.comp_app, NatTrans.id_app] using h
  apply (mono_iff_injective _).mpr
  intro x y hxy
  have hx := congrFun hs x
  have hy := congrFun hs y
  simpa only [types_comp_apply, types_id_apply] using
    hx.symm.trans ((congrArg (((evaluation K W v).app n).app q) hxy).trans hy)

#print axioms evaluation_row_joyalWeak_at
#print axioms evaluation_row_joyalWeak
#print axioms constantSection_row_joyalWeak
#print axioms unit_row_joyalWeak
#print axioms unit_cssWeak
#print axioms unit_mono

end
end DaggerModels.PartII.OrdinaryPrecompletionUnitCSSWeak
