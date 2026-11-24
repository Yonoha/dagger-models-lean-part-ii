import DaggerModelsPartII.ResolutionAdjunction
import DaggerModelsPartII.SegalLocalizers
import Mathlib.CategoryTheory.Functor.Currying

/-!
# Constant vertices of reversal dagger simplicial spaces

The direction swap identifies reversal simplicial spaces with simplicial
objects in dagger simplicial sets. The literal discrete dagger diagram is
left adjoint to evaluation at vertical degree zero.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels

universe u

namespace DaggerModels.PartII.ConstantVertexAdjunction

open SegalLocalizers

noncomputable section

/-- Swap the two simplicial directions and use the Part I presheaf
equivalence in each outer degree. -/
def directionEquivalence : ReverseDaggerSpace.{u} ≌ ResolutionDiagram.{u} :=
  (Functor.flipping :
    (ReverseSimplexᵒᵖ ⥤ SimplexCategoryᵒᵖ ⥤ Type u) ≌
      (SimplexCategoryᵒᵖ ⥤ ReverseSimplexᵒᵖ ⥤ Type u)).trans
    (daggerSSetEquivalencePresheaf.{u}.symm.congrRight)

/-- The literal discrete simplicial-space functor, called `δ` in Part II. -/
def delta : DaggerSSet.{u} ⥤ ReverseDaggerSpace.{u} := discreteDagger

/-- Evaluate the vertical simplicial direction at degree zero. -/
def vertexZero : ReverseDaggerSpace.{u} ⥤ DaggerSSet.{u} :=
  directionEquivalence.{u}.functor ⋙ evaluationAt 0

/-- The manuscript's zeroth-vertex functor. -/
def vertex : ReverseDaggerSpace.{u} ⥤ DaggerSSet.{u} := vertexZero

/-- The literal discrete functor is the constant resolution diagram after
the direction swap. This equality is definitional. -/
theorem delta_eq_constant_comp_inverse :
    delta.{u} = constantDiagram.{u} ⋙ directionEquivalence.{u}.inverse := rfl

/-- Evaluation at zero has exactly the manuscript's value `W_{m,0}`. -/
theorem vertexZero_value (W : ReverseDaggerSpace.{u})
    (m : ReverseSimplexᵒᵖ) :
    (DaggerSSet.toPresheaf.obj (vertexZero.{u}.obj W)).obj m =
      (W.obj m).obj (op ⦋0⦌) := rfl

/-- The discrete diagram has the same dagger simplex in every vertical degree. -/
theorem delta_value (X : DaggerSSet.{u}) (m : ReverseSimplexᵒᵖ)
    (k : SimplexCategoryᵒᵖ) :
    ((delta.{u}.obj X).obj m).obj k =
      (DaggerSSet.toPresheaf.obj X).obj m := rfl

/-- The right adjoint evaluates a map at vertical degree zero. -/
theorem vertexZero_map_value {W V : ReverseDaggerSpace.{u}} (f : W ⟶ V)
    (m : ReverseSimplexᵒᵖ) :
    (DaggerSSet.toPresheaf.map (vertexZero.{u}.map f)).app m =
      (f.app m).app (op ⦋0⦌) := rfl

/-- Under the direction-swap equivalence, the literal `δ` is the constant
resolution diagram functor, as in `jt.lem.c-delta` (2). -/
def deltaDirectionIso :
    delta.{u} ⋙ directionEquivalence.{u}.functor ≅ constantDiagram.{u} := by
  rw [delta_eq_constant_comp_inverse]
  exact (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft constantDiagram.{u} directionEquivalence.{u}.counitIso ≪≫
      constantDiagram.{u}.rightUnitor

/-- The right adjoint becomes evaluation at vertical degree zero under the
same direction swap. -/
theorem vertexZero_eq_direction_evaluation :
    vertexZero.{u} = directionEquivalence.{u}.functor ⋙ evaluationAt 0 := rfl

/-- The zeroth-vertex functor corresponds to evaluation at zero. -/
def vertexDirectionIso :
    vertex.{u} ≅ directionEquivalence.{u}.functor ⋙ evaluationAt 0 :=
  Iso.refl _

/-- The constant-vertex adjunction of `jt.lem.c-delta` (1). -/
def deltaVertexAdjunction : delta.{u} ⊣ vertexZero.{u} := by
  change constantDiagram.{u} ⋙ directionEquivalence.{u}.inverse ⊣
    directionEquivalence.{u}.functor ⋙ evaluationAt 0
  exact constantEvaluationAdjunction.{u}.comp
    directionEquivalence.{u}.symm.toAdjunction

/-- The constant-vertex adjunction under the manuscript's functor names. -/
def adjunction : delta.{u} ⊣ vertex.{u} := deltaVertexAdjunction

end

end DaggerModels.PartII.ConstantVertexAdjunction
