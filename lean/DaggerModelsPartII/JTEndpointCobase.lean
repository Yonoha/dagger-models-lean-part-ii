import OriginalEquivalenceModelTransport
import DaggerModelsPartII.NativeOverModelCompatibility
import Mathlib.AlgebraicTopology.ModelCategory.Opposite
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.CategoryTheory.WithTerminal.Cone
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.AlgebraicTopology.SimplexCategory.Defs

/-!
# Endpoint undercategory and cosimplicial cobase change

The native overcategory model structure and the exact equivalence with an
opposite undercategory supply the undercategory model. Its weak equivalences,
cofibrations and fibrations are detected on the literal right component.
The categorical endpoint cobase is a pushout of cosimplicial diagrams, and
left properness gives its pointwise weak comparison under the stated hypotheses.
-/

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MorphismProperty
  Opposite

universe v u
namespace DaggerModels.PartII.JTEndpointCobase
noncomputable section

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasLimits C] [HasColimits C]

/-- The model structure on arrows out of `B`, with all three arrow classes
recognized by their literal right components. -/
noncomputable def underModel (B : C) : ModelCategory (Under B) := by
  letI : ModelCategory Cᵒᵖ := inferInstance
  letI : ModelCategory (Over (op B)) := ModelCategory.over (op B)
  letI : ModelCategory (Over (op B))ᵒᵖ := inferInstance
  letI : CategoryWithWeakEquivalences (Under B) :=
    { weakEquivalences := (weakEquivalences C).under }
  letI : CategoryWithCofibrations (Under B) :=
    { cofibrations := (cofibrations C).under }
  letI : CategoryWithFibrations (Under B) :=
    { fibrations := (fibrations C).under }
  let E₀ : Under B ≌ Under (op (op B)) :=
    Under.postEquiv B ((opOpEquivalence C).symm)
  let E₁ : Under (op (op B)) ≌ (Over (op B))ᵒᵖ :=
    Under.opEquivOpOver (op B)
  let E : Under B ≌ (Over (op B))ᵒᵖ := E₀.trans E₁
  apply DaggerOriginalEquivalenceModelTransport.transportModel E
  · ext X Y f
    change weakEquivalences C f.right ↔
      weakEquivalences (Over (op B))ᵒᵖ (E.functor.map f)
    rw [weakEquivalences_op, weakEquivalences_over_def]
    change weakEquivalences C f.right ↔ weakEquivalences Cᵒᵖ f.right.op
    rw [weakEquivalences_op]
    rfl
  · ext X Y f
    change fibrations C f.right ↔
      fibrations (Over (op B))ᵒᵖ (E.functor.map f)
    rw [fibrations_op, cofibrations_over_def]
    change fibrations C f.right ↔ cofibrations Cᵒᵖ f.right.op
    rw [cofibrations_op]
    rfl
  · ext X Y f
    change cofibrations C f.right ↔
      cofibrations (Over (op B))ᵒᵖ (E.functor.map f)
    rw [cofibrations_op, fibrations_over_def]
    change cofibrations C f.right ↔ fibrations Cᵒᵖ f.right.op
    rw [fibrations_op]
    rfl

/-- Weak equivalences in the transported undercategory model are detected on
the actual right component. -/
theorem underModel_weakEquivalences (B : C) :
    (underModel B).categoryWithWeakEquivalences.weakEquivalences =
      (weakEquivalences C).under := rfl

/-- Cofibrations in the transported undercategory model are detected on the
actual right component. -/
theorem underModel_cofibrations (B : C) :
    (underModel B).categoryWithCofibrations.cofibrations =
      (cofibrations C).under := rfl

/-- Fibrations in the transported undercategory model are detected on the
actual right component. -/
theorem underModel_fibrations (B : C) :
    (underModel B).categoryWithFibrations.fibrations =
      (fibrations C).under := rfl

/-- The variable-source endpoint cobase of a cosimplicial arrow `u`, along a
map from its source to a fixed endpoint object `B`. -/
def endpointCobase {S T : SimplexCategory ⥤ C} (u : S ⟶ T)
    (B : C) (a : S ⟶ (Functor.const SimplexCategory).obj B) :
    SimplexCategory ⥤ C :=
  pushout a u

/-- The literal inclusion of the fixed endpoint object in its cobase. -/
def endpointCobase_inl {S T : SimplexCategory ⥤ C} (u : S ⟶ T)
    (B : C) (a : S ⟶ (Functor.const SimplexCategory).obj B) :
    (Functor.const SimplexCategory).obj B ⟶ endpointCobase u B a :=
  pushout.inl a u

/-- The natural comparison from the original target of the arrow. -/
def endpointCobase_inr {S T : SimplexCategory ⥤ C} (u : S ⟶ T)
    (B : C) (a : S ⟶ (Functor.const SimplexCategory).obj B) :
    T ⟶ endpointCobase u B a :=
  pushout.inr a u

omit [HasLimits C] [HasColimits C] in
/-- At every cosimplicial index the endpoint cobase is the ordinary pushout
of the corresponding coefficient arrows. -/
theorem endpointCobase_isPushout_at {S T : SimplexCategory ⥤ C} (u : S ⟶ T)
    (B : C) (a : S ⟶ (Functor.const SimplexCategory).obj B)
    (k : SimplexCategory) :
    IsPushout (a.app k) (u.app k)
      ((endpointCobase_inl u B a).app k)
      ((endpointCobase_inr u B a).app k) := by
  exact (IsPushout.of_hasPushout a u).map
    ((evaluation SimplexCategory C).obj k)

omit [HasLimits C] [HasColimits C] in
/-- The pointwise comparison from the original target to the endpoint cobase
is weak when the attaching arrow is pointwise cofibrant and the endpoint map
is pointwise weak. This is the left-properness step, not the Reedy-frame step. -/
theorem endpointCobase_inr_weak
    (leftProper : ∀ {A B D P : C} {i : A ⟶ B} {k : A ⟶ D}
      {l : B ⟶ P} {r : D ⟶ P},
      IsPushout i k l r → cofibrations C i →
        weakEquivalences C k → weakEquivalences C l)
    {S T : SimplexCategory ⥤ C} (u : S ⟶ T)
    (B : C) (a : S ⟶ (Functor.const SimplexCategory).obj B)
    (hu : ∀ k, cofibrations C (u.app k))
    (ha : ∀ k, weakEquivalences C (a.app k))
    (k : SimplexCategory) :
    weakEquivalences C ((endpointCobase_inr u B a).app k) :=
  leftProper (endpointCobase_isPushout_at u B a k).flip (hu k) (ha k)

end
end DaggerModels.PartII.JTEndpointCobase
