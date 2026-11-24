import DaggerModelsPartII.JTRawFiberToDecoratedIndex
import DaggerModelsPartII.DecoratedRawUnitHomCalibration
import DaggerModelsPartII.DecoratedCylinderNecklacePresentation

/-! The actual ordered-label evaluator on the strict raw one-edge fiber. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerNativeSimplicialReplacement DaggerNativeSimplicialReplacementReindex
open DaggerSSetGluing
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTRawFiberEvaluatorComparison

open JTGtildeOrderedFiberAction (sourceRow)
open JTProjectiveOrderedFiberComparison (targetVertices)
open JTRawFiberToDecoratedIndex (toDecorated toDecorated_weak)
open DecoratedRawUnitHomCalibration (wholeBarPostRawAtP postRawRightMapAtP)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

variable (W : Source)
variable (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌))

private abbrev a := (targetVertices W x y).1
private abbrev b := (targetVertices W x y).2

private abbrev labelFunctor := toDecorated W (a W x y) (b W x y)

private abbrev weights := DecoratedNecklaceHomDiagram.cylinderHomDiagram W (a W x y) (b W x y)

/-- Keep the entire original cylinder Hom weight along every strict-fiber label. -/
def strictFiberBar : SSet.{0} :=
  DaggerBisimplicialDiagonal.diag (replacement (labelFunctor W x y ⋙ weights W x y))

/-- Reindex every complete strict-fiber chain by its literal labels. -/
def toEvaluatorBar : strictFiberBar W x y ⟶
    DecoratedNecklaceHomBar.cylinderBar W (a W x y) (b W x y) :=
  diagonalReindex (labelFunctor W x y) (weights W x y)

/-- This exact bar reindexing is weak because the actual label-index map is weak
and the original cylinder Hom weights are contractible. -/
theorem toEvaluatorBar_weak
    (hW : @IsFibrant Source _ SegalLocalizers.injectiveSegalModel.categoryWithFibrations _ W) :
    WeakEquivalence (toEvaluatorBar W x y) :=
  (weakEquivalence_iff_GW _).mpr
    (diagonalReindex_GW (labelFunctor W x y) (weights W x y)
      ((weakEquivalence_iff_GW _).mp (toDecorated_weak W (a W x y) (b W x y) hW))
      (DecoratedCylinderNecklacePresentation.cylinderHom_point_GW W (a W x y) (b W x y)))

/-- The entire original evaluation after reindexing is the augmentation
of the full pulled-back rawG cocone. -/
theorem evaluator_triangle :
    toEvaluatorBar W x y ≫ wholeBarPostRawAtP W x y =
      diagonalAugmentation (labelFunctor W x y ⋙ weights W x y)
        (Functor.whiskerLeft (labelFunctor W x y) (postRawRightMapAtP W x y)) := by
  rw [DecoratedRawUnitHomCalibration.wholeBarPostRaw_augmentation]
  exact augmentation_square (labelFunctor W x y) (weights W x y) (postRawRightMapAtP W x y)

/-- On the actual strict-fiber bar, the augmented rawG map is weak if and
only if the original decorated evaluator is weak. -/
theorem restricted_evaluator_weak_iff
    (hW : @IsFibrant Source _ SegalLocalizers.injectiveSegalModel.categoryWithFibrations _ W) :
    WeakEquivalence (diagonalAugmentation (labelFunctor W x y ⋙ weights W x y)
        (Functor.whiskerLeft (labelFunctor W x y) (postRawRightMapAtP W x y))) ↔
      WeakEquivalence (DecoratedNecklaceHomBar.evaluator W (a W x y) (b W x y)) := by
  haveI := toEvaluatorBar_weak W x y hW
  rw [← evaluator_triangle]
  exact (weakEquivalence_precomp_iff _ _).trans
    (DecoratedRawUnitHomCalibration.wholeBarPostRaw_weak_iff W x y)

end

end DaggerModels.PartII.JTRawFiberEvaluatorComparison
