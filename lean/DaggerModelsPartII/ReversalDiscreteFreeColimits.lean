import DaggerModelsPartII.SegalLocalizers
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Colimits of the discrete free dagger presheaf functor

The actual functor `δ ∘ Fdag` preserves colimits, so the two ordinary
outer-face and spine pushout squares remain pushout squares in reversal
dagger simplicial spaces. It also preserves monomorphisms.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerModels.PartII.ReversalDiscreteFreeColimits

open SegalLocalizers

noncomputable section

/-- The manuscript's actual discrete free dagger presheaf functor. -/
def discreteFree : SSet.{u} ⥤ ReverseDaggerSpace.{u} :=
  freeDagger ⋙ discreteDagger

/-- Discretization of dagger presheaves preserves pushouts. -/
theorem discreteDagger_preservesPushouts :
    PreservesColimitsOfShape WalkingSpan discreteDagger.{u} := by
  letI : PreservesColimitsOfShape WalkingSpan DaggerSSet.toPresheaf.{u} :=
    daggerSSetEquivalencePresheaf.toAdjunction.leftAdjoint_preservesColimits.preservesColimitsOfShape
  letI : PreservesColimitsOfShape WalkingSpan
      (SimplicialObject.const (Type u)) :=
    (CategoryTheory.Limits.preservesColimits_const
      (D := SimplexCategoryᵒᵖ)).preservesColimitsOfShape
  letI : PreservesColimitsOfShape WalkingSpan
      ((Functor.whiskeringRight ReverseSimplexᵒᵖ (Type u) SSet.{u}).obj
        (SimplicialObject.const (Type u))) := inferInstance
  change PreservesColimitsOfShape WalkingSpan
    (DaggerSSet.toPresheaf.{u} ⋙
      (Functor.whiskeringRight ReverseSimplexᵒᵖ (Type u) SSet.{u}).obj
        (SimplicialObject.const (Type u)))
  infer_instance

/-- The composite `δ ∘ Fdag` preserves pushouts. -/
theorem discreteFree_preservesPushouts :
    PreservesColimitsOfShape WalkingSpan discreteFree.{u} := by
  letI : PreservesColimitsOfShape WalkingSpan freeDagger.{u} :=
    freeDaggerAdjunction.leftAdjoint_preservesColimits.preservesColimitsOfShape
  letI : PreservesColimitsOfShape WalkingSpan discreteDagger.{u} :=
    discreteDagger_preservesPushouts
  change PreservesColimitsOfShape WalkingSpan (freeDagger.{u} ⋙ discreteDagger.{u})
  infer_instance

/-- A pushout square remains a pushout after discrete free dagger completion. -/
theorem map_isPushout {A B D P : SSet.{u}} {i : A ⟶ B} {k : A ⟶ D}
    {l : B ⟶ P} {r : D ⟶ P} (sq : IsPushout i k l r) :
    IsPushout (discreteFree.map i) (discreteFree.map k)
      (discreteFree.map l) (discreteFree.map r) := by
  letI : PreservesColimitsOfShape WalkingSpan discreteFree.{u} :=
    discreteFree_preservesPushouts
  exact sq.map discreteFree

/-- A simplicial monomorphism stays monic under discrete free dagger completion. -/
theorem map_mono {A B : SSet.{u}} (i : A ⟶ B) [Mono i] :
    Mono (discreteFree.map i) := by
  letI : Mono (freeDagger.map i) := (freeDagger_map_isFreeCofibration i).1
  change Mono (discreteDagger.map (freeDagger.map i))
  exact discreteDagger_map_mono _

end

end DaggerModels.PartII.ReversalDiscreteFreeColimits
