import Mathlib.CategoryTheory.Action.Limits
import Mathlib.CategoryTheory.Limits.Shapes.SingleObj
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.CategoryTheory.Limits.Presheaf

/-!
# Strict orbits of a categorical group action

The orbit object is the colimit of the corresponding one-object diagram.
This definition applies equally to simplicial sets and to simplicial-set
diagrams. It makes the colimit preservation needed for the Borel filtration
independent of any model structure on actions.
-/

set_option autoImplicit false

open CategoryTheory Limits

universe w v u

namespace DaggerModels.PartII.ActionStrictOrbits

noncomputable section

variable (V : Type u) [Category.{v} V] [HasColimits V]
  (G : Type w) [Group G] [HasColimitsOfShape (SingleObj G) V]

/-- Strict orbit objects, functorial in an action. -/
def orbit : Action V G ⥤ V :=
  (Action.functorCategoryEquivalence V G).functor ⋙ colim

/-- The constant diagram, viewed as a trivial group action. -/
def trivial : V ⥤ Action V G :=
  Functor.const (SingleObj G) ⋙ (Action.functorCategoryEquivalence V G).inverse

/-- The strict orbit functor is left adjoint to the trivial-action functor. -/
def orbitAdjunction : orbit V G ⊣ trivial V G :=
  (Action.functorCategoryEquivalence V G).toAdjunction.comp colimConstAdj

/-- Strict orbits preserve colimits because the action equivalence and
one-object colimit functor are left adjoints. -/
instance orbit_preservesColimits : PreservesColimits (orbit V G) := by
  unfold orbit
  infer_instance

open Opposite

/-- A strict orbit of a simplicial action is, in each degree, the ordinary
quotient of the underlying simplices by that degree's group action. -/
def simplicialDegreeEquiv {G : Type u} [Group G]
    [HasColimitsOfShape (SingleObj G) SSet.{u}]
    (X : Action SSet.{u} G) (n : SimplexCategoryᵒᵖ) :
    ((orbit SSet.{u} G).obj X).obj n ≃
      (let J := (Action.functorCategoryEquivalence SSet.{u} G).functor.obj X
       let Jn := J ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj n
       MulAction.orbitRel.Quotient G (Jn.obj (SingleObj.star G))) :=
  let J := (Action.functorCategoryEquivalence SSet.{u} G).functor.obj X
  (colimitObjIsoColimitCompEvaluation J n).toEquiv.trans
    (SingleObj.Types.colimitEquivQuotient
      (J ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj n))

end

end DaggerModels.PartII.ActionStrictOrbits
