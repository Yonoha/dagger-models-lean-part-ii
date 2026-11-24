import DaggerModelsPartII.WeakFunctorBrown
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Coproduct weakness from the actual cofibrant Brown lemma

Fixing one coproduct variable sends trivial cofibrations to weak maps by
native cobase change. Brown therefore preserves weak maps between cofibrant
objects. Braiding gives the other variable, and composition gives the
actual two-variable coproduct map. The required source and target
cofibrancy assumptions are explicit.
-/

set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra

universe v u
namespace DaggerModels.PartII.CoproductWeakOnCofibrant

noncomputable section

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasBinaryCoproducts C]

/-- Coproduct with an arbitrary fixed object preserves weak maps between
cofibrant objects in the varying variable. -/
theorem map_id_weak (T : C) {X Y : C} [IsCofibrant X] [IsCofibrant Y]
    (f : X ⟶ Y) (hf : weakEquivalences C f) :
    weakEquivalences C (coprod.map f (𝟙 T)) := by
  let F : C ⥤ C := (coprod.functor (C := C)).flip.obj T
  apply WeakFunctorBrown.map_weak_on_cofibrant F (weakEquivalences C) ?_ f hf
  intro A B i hi
  have h : trivialCofibrations C (coprod.map i (𝟙 T)) :=
    MorphismProperty.of_isPushout (IsPushout.of_coprod_inl_with_id i T) hi
  exact h.2

/-- The right-variable version uses the native coproduct braiding. -/
theorem id_map_weak (T : C) {X Y : C} [IsCofibrant X] [IsCofibrant Y]
    (f : X ⟶ Y) (hf : weakEquivalences C f) :
    weakEquivalences C (coprod.map (𝟙 T) f) := by
  let e : Arrow.mk (coprod.map f (𝟙 T)) ≅ Arrow.mk (coprod.map (𝟙 T) f) :=
    Arrow.isoMk (coprod.braiding X T) (coprod.braiding Y T) (by
      apply coprod.hom_ext <;> simp [coprod.braiding])
  exact ((weakEquivalences C).arrow_mk_iso_iff e).1 (map_id_weak T f hf)

/-- The literal binary coproduct map is weak when both component weak maps
are between cofibrant objects. -/
theorem map_weak {X Y X' Y' : C}
    [IsCofibrant X] [IsCofibrant Y] [IsCofibrant X'] [IsCofibrant Y']
    (f : X ⟶ Y) (g : X' ⟶ Y')
    (hf : weakEquivalences C f) (hg : weakEquivalences C g) :
    weakEquivalences C (coprod.map f g) := by
  have h := (weakEquivalences C).comp_mem _ _
    (map_id_weak X' f hf) (id_map_weak Y g hg)
  simpa only [coprod.map_map, Category.comp_id, Category.id_comp] using h

end

end DaggerModels.PartII.CoproductWeakOnCofibrant
