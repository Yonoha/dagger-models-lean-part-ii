import DaggerModelsPartII.OrdinaryJTRealization
import DaggerModelsPartII.SegalLocalizers
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Products.Basic

/-!
# Restriction of reversal simplicial spaces to the ordinary JT input

The functor restricts the horizontal reversal simplex index to ordinary
monotone maps, then uncarries the resulting two simplicial directions.
-/

set_option autoImplicit false

open CategoryTheory Opposite DaggerModels

namespace DaggerModels.PartII.JTReversalInput

open SegalLocalizers OrdinaryJTRealization

noncomputable section

/-- Forget horizontal reversal while retaining both literal simplicial degrees. -/
def ordinaryInput : ReverseDaggerSpace.{0} ⥤ BiPresheaf :=
  ((Functor.whiskeringLeft _ _ _).obj ReverseSimplex.inclusion.op) ⋙
    Functor.uncurry ⋙
      ((Functor.whiskeringLeft _ _ _).obj
        (CategoryTheory.prodOpEquiv (C := SimplexCategory)
          (D := SimplexCategory)).functor)

@[simp] theorem ordinaryInput_obj_obj (W : ReverseDaggerSpace.{0})
    (m k : SimplexCategory) :
    (ordinaryInput.obj W).obj (op (m, k)) =
      (W.obj (op (ReverseSimplex.inclusion.obj m))).obj (op k) := rfl

@[simp] theorem ordinaryInput_map_app (W V : ReverseDaggerSpace.{0})
    (f : W ⟶ V) (m k : SimplexCategory) :
    (ordinaryInput.map f).app (op (m, k)) =
      (f.app (op (ReverseSimplex.inclusion.obj m))).app (op k) := rfl

end

end DaggerModels.PartII.JTReversalInput
