import DaggerModelsPartII.UnderReedyCriterion
import DaggerModelsPartII.JTEndpointCobase
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# Reedy cofibrancy of the endpoint cobase

The opposite of a cosimplicial relative Reedy cofibration is a relative
matching fibration. The endpoint cobase becomes a pullback after taking
opposites. The checked undercategory criterion then recognizes the Reedy
cofibrancy of the actual diagram under the fixed boundary, including degree
zero.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite Simplicial

universe v u

namespace DaggerModels.PartII.EndpointCobaseReedy

noncomputable section

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasLimits C] [HasColimits C]

omit [ModelCategory C] [HasLimits C] [HasColimits C] in
private theorem isPullback_of_pointwise
    {K : Type*} [Category K] {A B D E : K ⥤ Cᵒᵖ}
    {t : A ⟶ B} {l : A ⟶ D} {r : B ⟶ E} {b : D ⟶ E}
    (h : ∀ k : K, IsPullback (t.app k) (l.app k) (r.app k) (b.app k)) :
    IsPullback t l r b := by
  have w : t ≫ r = l ≫ b := by
    ext k
    exact (h k).w
  apply IsPullback.of_isLimit (c := PullbackCone.mk t l w)
  apply evaluationJointlyReflectsLimits
  intro k
  exact (isLimitMapConePullbackConeEquiv
    ((evaluation K Cᵒᵖ).obj k) w).symm (by
      change IsLimit (h k).cone
      exact (h k).isLimit)

/-- Cobase change of a cosimplicial relative Reedy cofibration, expressed
as the matching property of its opposite, retains that property. -/
theorem endpointCobase_inl_relativeMatching
    {S T : SimplexCategory ⥤ C} (u : S ⟶ T) (B : C)
    (a : S ⟶ (Functor.const SimplexCategory).obj B)
    (hu : reedyMatchingProperty (fibrations Cᵒᵖ) (NatTrans.op u)) :
    reedyMatchingProperty (fibrations Cᵒᵖ)
      (NatTrans.op (JTEndpointCobase.endpointCobase_inl u B a)) := by
  letI : ModelCategory Cᵒᵖ := inferInstance
  let P := reedyMatchingProperty (fibrations Cᵒᵖ)
  letI : IsWeakFactorizationSystem
      (reedyLatchingProperty (trivialCofibrations Cᵒᵖ)) P :=
    reedyRelativeWeakFactorizationSystem _ _
  letI : P.IsStableUnderBaseChange := by
    change (reedyMatchingProperty (fibrations Cᵒᵖ)).IsStableUnderBaseChange
    rw [← rlp_eq_of_wfs
      (reedyLatchingProperty (trivialCofibrations Cᵒᵖ))
      (reedyMatchingProperty (fibrations Cᵒᵖ))]
    infer_instance
  let b := JTEndpointCobase.endpointCobase_inl u B a
  let r := JTEndpointCobase.endpointCobase_inr u B a
  have hpoint (k : SimplexCategoryᵒᵖ) :
      IsPullback ((NatTrans.op r).app k) ((NatTrans.op b).app k)
        ((NatTrans.op u).app k) ((NatTrans.op a).app k) := by
    simpa only [NatTrans.op_app] using
      (JTEndpointCobase.endpointCobase_isPushout_at u B a k.unop).op
  have hsq : IsPullback (NatTrans.op r) (NatTrans.op b)
      (NatTrans.op u) (NatTrans.op a) :=
    isPullback_of_pointwise hpoint
  exact P.of_isPullback hsq hu

/-- The actual endpoint cobase under B is Reedy cofibrant in the native
opposite Reedy model. No matching-limit preservation by `Under.forget` is
assumed; the fixed endpoint appears in the relative matching pullback. -/
theorem endpointCobase_reedyCofibrant
    {S T : SimplexCategory ⥤ C} (u : S ⟶ T) (B : C)
    (a : S ⟶ (Functor.const SimplexCategory).obj B)
    (hu : reedyMatchingProperty (fibrations Cᵒᵖ) (NatTrans.op u)) :
    letI : ModelCategory (Under B) := JTEndpointCobase.underModel B
    letI : ModelCategory (Under B)ᵒᵖ := inferInstance
    letI : ModelCategory (SimplexCategoryᵒᵖ ⥤ (Under B)ᵒᵖ) :=
      simplicialReedyModelCategory (Under B)ᵒᵖ
    IsFibrant ((Under.lift (JTEndpointCobase.endpointCobase u B a)
      (JTEndpointCobase.endpointCobase_inl u B a)).op) := by
  letI : ModelCategory (Under B) := JTEndpointCobase.underModel B
  letI : ModelCategory (Under B)ᵒᵖ := inferInstance
  letI : ModelCategory (SimplexCategoryᵒᵖ ⥤ (Under B)ᵒᵖ) :=
    simplicialReedyModelCategory (Under B)ᵒᵖ
  let b := JTEndpointCobase.endpointCobase_inl u B a
  let U := Under.lift (JTEndpointCobase.endpointCobase u B a) b
  have hb : reedyMatchingProperty (fibrations Cᵒᵖ) (NatTrans.op b) :=
    endpointCobase_inl_relativeMatching u B a hu
  have hstructure :
      OverMatchingRelative.structureMap (op B)
        (U.op ⋙ UnderReedyCriterion.underOppositeToOver B) = NatTrans.op b := by
    rfl
  apply (UnderReedyCriterion.reedyFibrant_iff_relativeMatching B U.op).2
  simpa only [hstructure] using hb

end

end DaggerModels.PartII.EndpointCobaseReedy
