import DaggerModelsPartII.JTEndpointRowGraphOperators

/-! Mixed graph arrows into one chosen graph carry a common exact coefficient. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTEndpointGraphCoefficientSlice

open OrdinaryJTRealization (realization)
open JTReversalInput JTProjectiveOrderedFiberComparison JTMixedGraphEndpointLifts
open JTEndpointSimplexSlice JTEndpointRowGraphResolution JTEndpointRowGraphOperators

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Δ (m : SimplexCategory) := SSet.stdSimplex.{0}.obj m
private abbrev rows (W : Source) := JTRealizationDiagonal.ordinaryCurry.obj (ordinaryInput.obj W)

variable {W : Source} {d : ℕ} {q : Δ ⦋d⦌ ⟶ realization.obj (ordinaryInput.obj W)}

/-- Covariant mixed graph arrows point from a smaller source to the larger source. -/
abbrev MixedGraphs (q : Δ ⦋d⦌ ⟶ realization.obj (ordinaryInput.obj W)) :=
  (Resolution q)ᵒᵖ

/-- Forget the coefficient parameter while retaining the exact horizontal operator. -/
abbrev horizontal : MixedGraphs q ⥤ Slice d :=
  (Grothendieck.forget (diagram q)).leftOp

/-- Retain the full coefficient operator of every mixed arrow. -/
def coefficientDegree : MixedGraphs q ⥤ SimplexCategory where
  obj A := (graph A.unop).obj.degree
  map f := operator f.unop
  map_id A := operator_id A.unop
  map_comp f g := operator_comp g.unop f.unop

variable (P : MixedGraphs q)

/-- Graphs supplied with an exact arrow to the chosen parent all share its coefficient. -/
abbrev coefficients : Over P ⥤ Over (coefficientDegree.obj P) :=
  Over.post coefficientDegree

/-- The actual horizontal code of each graph, with its two outer beads. -/
abbrev codes : Over P ⥤ NecklaceCode :=
  Over.forget P ⋙ horizontal ⋙ paddedSource d

/-- At an object of the slice, restrict the parent coefficient horizontally. -/
abbrev parentRow (A : Over P) :
    Δ (coefficientDegree.obj P) ⟶ row W (horizontalDegree A.left.unop) :=
  graphCoefficient P.unop ≫ (rows W).map A.hom.unop.base.unop.left.1.op

/-- Pulling the actual parent coefficient back along the mixed map gives the original child. -/
theorem coefficient_factor (A : Over P) :
    SSet.stdSimplex.map ((coefficients P).obj A).hom ≫ parentRow P A =
      graphCoefficient A.left.unop := by
  let a : horizontalDegree A.left.unop ⟶ horizontalDegree P.unop :=
    A.hom.unop.base.unop.left.1
  let b : (graph A.left.unop).obj.degree ⟶ (graph P.unop).obj.degree := operator A.hom.unop
  let r : row W (horizontalDegree P.unop) ⟶ row W (horizontalDegree A.left.unop) :=
    (rows W).map a.op
  let c : (row W (horizontalDegree P.unop)).obj (op (graph P.unop).obj.degree) :=
    (graph P.unop).obj.coefficient
  change SSet.stdSimplex.map b ≫ (SSet.yonedaEquiv.symm c ≫ r) = _
  rw [SSet.yonedaEquiv_symm_comp, ← SSet.yonedaEquiv_symm_map]
  exact congrArg (SSet.yonedaEquiv (X := row W (horizontalDegree A.left.unop))
    (n := (graph A.left.unop).obj.degree)).symm A.hom.unop.fiber.unop.hom.coefficient

/-- The same factor retains the entire original codiscrete parameter. -/
theorem parameter_factor (A : Over P) :
    (graph A.left.unop).obj.parameter ≫ GroupoidSimplex.parameter.map ((coefficients P).obj A).hom =
      SSet.stdSimplex.map A.hom.unop.base.unop.left.1 ≫ (graph P.unop).obj.parameter :=
  A.hom.unop.fiber.unop.hom.parameter

/-- (Co)variance is controlled by the original slice triangle in the horizontal direction. -/
theorem parentRow_natural {A B : Over P} (f : A ⟶ B) :
    parentRow P B ≫ (rows W).map f.left.unop.base.unop.left.1.op = parentRow P A := by
  have h := congrArg
    (fun u : A.left ⟶ P ↦ u.unop.base.unop.left.1) (Over.w f)
  change f.left.unop.base.unop.left.1 ≫ B.hom.unop.base.unop.left.1 =
    A.hom.unop.base.unop.left.1 at h
  unfold parentRow
  rw [Category.assoc, ← Functor.map_comp, ← op_comp, h]

/-- The parent's whole coefficient restricts at each horizontal vertex. -/
theorem parentRow_vertex (A : Over P) (i : Fin ((horizontalDegree A.left.unop).len + 1)) :
    parentRow P A ≫ rowVertex W (horizontalDegree A.left.unop) i =
      graphCoefficient P.unop ≫ rowVertex W (horizontalDegree P.unop)
        (A.hom.unop.base.unop.left.1.toOrderHom i) := by
  let a : horizontalDegree A.left.unop ⟶ horizontalDegree P.unop :=
    A.hom.unop.base.unop.left.1
  have h : SimplexCategory.const ⦋0⦌ (horizontalDegree A.left.unop) i ≫ a =
      SimplexCategory.const ⦋0⦌ (horizontalDegree P.unop) (a.toOrderHom i) :=
    SimplexCategory.const_comp _ a i
  change (graphCoefficient P.unop ≫ (rows W).map a.op) ≫
    (rows W).map (SimplexCategory.const ⦋0⦌ _ i).op = _
  rw [Category.assoc, ← Functor.map_comp, ← op_comp, h]
  rfl

end
end DaggerModels.PartII.JTEndpointGraphCoefficientSlice
