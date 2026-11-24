import DaggerModelsPartII.OrderedSingleEdgeElements
import DaggerModelsPartII.TotalElementsWeakComparison
import DaggerModelsPartII.OrderedLabelTotalNerveWeakComparison
import DaggerModelsPartII.JTRawSingleOrderedLabelIso

/-! The original strict endpoint fiber maps by its literal labels to the decorated index. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTRawFiberToDecoratedIndex

open OrderedNecklaceLabelDiagram OrderedNecklaceVertexPoints
open JTProjectiveOrderedFiberComparison OrderedSimplexEndpointFiber
open DaggerChosenRigidificationNecklace.NecklaceCode
open TotalElementsWeakComparison

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)

variable (W : Source) (x y : Vertex W)

private abbrev strictFiber := pullback (endpointArrow W) (point W x y)
private abbrev b := boundaryPoint W x y
private abbrev singleIso := orderedSingleFiberIso W x y

/-- Send every actual strict-fiber simplex to the same native single-edge label.
The functor retains its whole parameter simplex and its original operators. -/
def toDecorated :
    (strictFiber W x y).Elementsᵒᵖ ⥤ OrderedLabelElements.Index W (b W x y) :=
  ((Functor.elementsFunctor.map (singleIso W x y).inv).toFunctor ⋙
    OrderedSingleEdgeElements.inclusion W (b W x y) ⋙
    totalMap (orderedRestriction W (b W x y)) ⋙
    OrderedLabelSimplexResolution.totalToOrdered W (b W x y)).op

/-- Each object is the exact single-edge label already calibrated against rawG. -/
theorem toDecorated_obj (k : SimplexCategory)
    (z : (strictFiber W x y).obj (op k)) :
    (toDecorated W x y).obj (op ((strictFiber W x y).elementsMk (op k) z)) =
      OrderedLabelElements.mk W (b W x y) (single 1) k
        (JTRawSingleOrderedLabelIso.nativeLabelOfRawFiber W x y k z) := rfl

/-- For injective Segal-local fibrant input, the literal single-edge functor
induces a weak equivalence to the whole original decorated label nerve. -/
theorem toDecorated_weak
    (hW : @IsFibrant Source _ SegalLocalizers.injectiveSegalModel.categoryWithFibrations _ W) :
    WeakEquivalence (nerveMap (toDecorated W x y)) := by
  let i := (Functor.elementsFunctor.map (singleIso W x y).inv).toFunctor
  let j := OrderedSingleEdgeElements.inclusion W (b W x y)
  let t := totalMap (orderedRestriction W (b W x y))
  let c := OrderedLabelSimplexResolution.totalToOrdered W (b W x y)
  haveI : WeakEquivalence (nerveMap i) := by
    change WeakEquivalence (nerveFunctor.map (Functor.elementsFunctor.map (singleIso W x y).inv))
    infer_instance
  haveI : WeakEquivalence (nerveMap j) := OrderedSingleEdgeElements.inclusion_weak W (b W x y)
  haveI : WeakEquivalence (nerveMap t) :=
    totalMap_weak (orderedRestriction W (b W x y)) fun d ↦
      ((mem_trivialFibrations_iff _).mp (orderedRestriction_trivialFibration W hW
        (b W x y) d.unop)).2
  haveI : WeakEquivalence (nerveMap c) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence
      (OrderedLabelTotalNerveWeakComparison.coordinateEquivalence W (b W x y)).functor
  change WeakEquivalence (nerveMap (i ⋙ j ⋙ t ⋙ c).op)
  apply (nerveMap_op_iff _).mpr
  change WeakEquivalence (nerveMap i ≫ nerveMap j ≫ nerveMap t ≫ nerveMap c)
  infer_instance

end

end DaggerModels.PartII.JTRawFiberToDecoratedIndex
