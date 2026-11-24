import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Lifting against a fixed parameter in a parametrized adjunction

At an initial-to-parameter arrow, the pushout-product is the parameter
component itself. This exposes the lifting statement used with cofibrant
simplicial `EC₂`, without a model structure on the category of diagram actions.
-/

set_option autoImplicit false

open CategoryTheory Limits

universe u₁ u₂ u₃ v₁ v₂ v₃

namespace DaggerModels.PartII

noncomputable section

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [HasInitial C₂]
  (F : C₁ ⥤ C₂ ⥤ C₃) (G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂)
  {A B : C₁} (i : A ⟶ B) (E : C₂)
  (hA : IsInitial ((F.obj A).obj (⊥_ C₂)))
  (hB : IsInitial ((F.obj B).obj (⊥_ C₂)))

/-- At an initial scalar, the pushout-product domain is the source parameter value. -/
def initialParameterPushout : F.PushoutObjObj i (initial.to E) where
  pt := (F.obj A).obj E
  inl := hB.to _
  inr := 𝟙 _
  isPushout := by
    haveI : IsIso ((F.map i).app (⊥_ C₂)) := isIso_of_isInitial hA hB _
    apply IsPushout.of_horiz_isIso
    exact ⟨hA.hom_ext _ _⟩

theorem initialParameterPushout_ι :
    (initialParameterPushout F i E hA hB).ι = (F.map i).app E := by
  have h := (initialParameterPushout F i E hA hB).inr_ι
  simpa only [initialParameterPushout, Category.id_comp] using h

include hA hB in
/-- The fixed parameter's lifting problem is the initial-arrow lifting
problem against the genuine mapping corner. -/
theorem parametrized_initial_lifting_iff (adj : F ⊣₂ G)
    {Y Z : C₃} (p : Y ⟶ Z) (corner : G.PullbackObjObj i p) :
    HasLiftingProperty ((F.map i).app E) p ↔
      HasLiftingProperty (initial.to E) corner.π := by
  simpa only [initialParameterPushout_ι] using
    adj.hasLiftingProperty_iff (initialParameterPushout F i E hA hB) corner

end

end DaggerModels.PartII
