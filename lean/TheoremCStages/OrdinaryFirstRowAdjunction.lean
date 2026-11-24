import OrdinaryCSSLocalization
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Products.Basic

/-!
# The ordinary first-row adjunction

The vertical constant simplicial object is left adjoint to evaluation at
vertical degree zero because zero is terminal in `SimplexCategory`. This
adjunction is applied at every horizontal degree. Its counit is the actual
vertical collapse map, including the original horizontal simplicial-set
structure. No model-category or completeness premise enters this identity.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.OrdinaryFirstRowAdjunction

open OrdinaryCSSLocalization

noncomputable section

/-- Evaluation at the original vertical zero degree, retaining the entire
horizontal simplicial set. -/
def firstRow : Space ⥤ SSet.{0} :=
  (Functor.whiskeringRight SimplexCategoryᵒᵖ SSet.{0} (Type 0)).obj
    ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj (op ⦋0⦌))

/-- The first row is literally the vertical-zero slice of the flipped
bisimplicial set. -/
theorem firstRow_obj (W : Space) :
    firstRow.obj W = W.flip.obj (op ⦋0⦌) := rfl

/-- Its action on morphisms retains the original vertical-zero component. -/
theorem firstRow_map {W V : Space} (f : W ⟶ V) :
    firstRow.map f =
      ((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type 0)).map f).app
        (op ⦋0⦌) := rfl

private def verticalAdjunction :
    SimplicialObject.const (Type 0) ⊣
      (evaluation SimplexCategoryᵒᵖ (Type 0)).obj (op ⦋0⦌) where
  unit := (Functor.constCompEvaluationObj (Type 0) (op ⦋0⦌)).hom
  counit := {
    app := fun F => {
      app := fun k =>
        F.map (SimplexCategory.isTerminalZero.from k.unop).op
      naturality := by
        intro k l f
        simp only [Functor.comp_obj, Functor.const_obj_obj, Functor.id_obj,
          Functor.const_obj_map, Category.id_comp, ← Functor.map_comp]
        congr 1 }
    naturality := by
      intro F G η
      ext k a
      exact congrFun (η.naturality
        (SimplexCategory.isTerminalZero.from k.unop).op).symm a }

/-- The actual ordinary discrete simplicial-space functor is left adjoint
to literal first-row evaluation. -/
def adjunction : discrete ⊣ firstRow :=
  Adjunction.whiskerRight SimplexCategoryᵒᵖ verticalAdjunction

/-- At horizontal degree `q` and vertical degree `k`, the counit is the
original map induced by the terminal collapse `k ⟶ 0`. -/
theorem counit_app_app (W : Space) (q k : SimplexCategory) :
    ((adjunction.counit.app W).app (op q)).app (op k) =
      (W.flip.map (SimplexCategory.isTerminalZero.from k).op).app (op q) := by
  rfl

#print axioms firstRow
#print axioms adjunction
#print axioms counit_app_app

end

end DaggerModels.PartII.OrdinaryFirstRowAdjunction
