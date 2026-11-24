import BisimplicialCommaParameterProjection
import DaggerModelsPartII.DiagonalRecognition

/-!
# Pointed weak comparison with the original and auxiliary diagonals

The middle arrow is the original comma fiber bar over its whole parameter
bar. Both maps out of its chosen homotopy fiber retain the supplied point.
Calibration of that point with the original endpoint pair remains separate.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory HomotopicalAlgebra
open DaggerNativeBisimplicialHorizontalMapping (BiSSet)
open DaggerNativeBisimplicialDiagonal (diagonalFunctor)
open DaggerNativeSimplicialReplacement (replacement diagonalProjection)
open DaggerNativeSimplicialReplacementWeightsChange (diagonalChange changeWeights)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.BisimplicialCommaChosenFiberSpan

open BisimplicialBaseSimplexFibers (fiberDiagram simplexProjection)
open BisimplicialBaseSimplexKanFibers (kanFiberDiagram)
open BisimplicialCommaDiagonalReconstruction
open ChosenHomotopyFiberComparison (chosenFiber)
open ChosenHomotopyFiberFunctor (chosenMap)

noncomputable section

/-- The original full strict-fiber bar over its whole simplex-parameter bar. -/
def barArrow (f : Arrow BiSSet.{0}) := diagonalChange (simplexProjection f)

/-- Both diagonal reconstruction maps form a square with the original arrow. -/
theorem original_square (f : Arrow BiSSet.{0}) :
    barArrow f ≫ diagonalFunctor.map (baseReconstruction f) =
      diagonalFunctor.map (totalReconstruction f) ≫ diagonalFunctor.map f.hom := by
  simpa only [diagonalFunctor.map_comp] using
    congrArg diagonalFunctor.map (reconstruction_square f)

/-- The pointwise Kan unit and parameter projection retain the full comma chain. -/
theorem auxiliary_square (f : Arrow BiSSet.{0}) :
    barArrow f ≫ diagonalProjection (parameterDiagram f) =
      diagonalChange (SimplicialReplacementPointwiseKan.kanUnit (fiberDiagram f)) ≫
        diagonalProjection (kanFiberDiagram f) :=
  (BisimplicialCommaParameterProjection.simplexProjection_projection_triangle f).trans
    (BisimplicialCommaParameterProjection.kanUnit_projection_triangle f).symm

/-- The actual chosen-fiber map to the original diagonal, at the supplied point. -/
def originalFiberComparison (f : Arrow BiSSet.{0}) {K : SSet.{0}}
    (b : K ⟶ DaggerBisimplicialDiagonal.diag (replacement (parameterDiagram f))) :
    chosenFiber (barArrow f) b ⟶
      chosenFiber (diagonalFunctor.map f.hom)
        (b ≫ diagonalFunctor.map (baseReconstruction f)) :=
  chosenMap (barArrow f) (diagonalFunctor.map f.hom)
    (diagonalFunctor.map (totalReconstruction f))
    (diagonalFunctor.map (baseReconstruction f)) (original_square f)
    b (b ≫ diagonalFunctor.map (baseReconstruction f)) rfl

/-- The original pointed diagonal comparison is weak without a Kan assumption. -/
theorem originalFiberComparison_weak (f : Arrow BiSSet.{0}) {K : SSet.{0}}
    (b : K ⟶ DaggerBisimplicialDiagonal.diag (replacement (parameterDiagram f))) :
    WeakEquivalence (originalFiberComparison f b) := by
  have : WeakEquivalence (diagonalFunctor.map (totalReconstruction f)) :=
    totalReconstruction_diagonal_weak f
  have : WeakEquivalence (diagonalFunctor.map (baseReconstruction f)) :=
    baseReconstruction_diagonal_weak f
  exact DiagonalRecognition.chosenMap_weak_of_weak_square _ _ _ _ _ _ _ _

/-- The actual chosen-fiber map to the Kan-value auxiliary projection. -/
def auxiliaryFiberComparison (f : Arrow BiSSet.{0}) {K : SSet.{0}}
    (b : K ⟶ DaggerBisimplicialDiagonal.diag (replacement (parameterDiagram f))) :
    chosenFiber (barArrow f) b ⟶
      chosenFiber (diagonalProjection (kanFiberDiagram f))
        (b ≫ diagonalProjection (parameterDiagram f)) :=
  chosenMap (barArrow f) (diagonalProjection (kanFiberDiagram f))
    (diagonalChange (SimplicialReplacementPointwiseKan.kanUnit (fiberDiagram f)))
    (diagonalProjection (parameterDiagram f)) (auxiliary_square f)
    b (b ≫ diagonalProjection (parameterDiagram f)) rfl

/-- The auxiliary pointed comparison is weak and retains exactly the same point. -/
theorem auxiliaryFiberComparison_weak (f : Arrow BiSSet.{0}) {K : SSet.{0}}
    (b : K ⟶ DaggerBisimplicialDiagonal.diag (replacement (parameterDiagram f))) :
    WeakEquivalence (auxiliaryFiberComparison f b) := by
  have : WeakEquivalence
      (diagonalChange (SimplicialReplacementPointwiseKan.kanUnit (fiberDiagram f))) :=
    SimplicialReplacementPointwiseKan.kanUnit_diagonal_weak (fiberDiagram f)
  have : WeakEquivalence (diagonalProjection (parameterDiagram f)) :=
    BisimplicialCommaParameterProjection.parameterProjection_weak f
  exact DiagonalRecognition.chosenMap_weak_of_weak_square _ _ _ _ _ _ _ _

#print axioms original_square
#print axioms auxiliary_square
#print axioms originalFiberComparison_weak
#print axioms auxiliaryFiberComparison_weak

end

end DaggerModels.PartII.BisimplicialCommaChosenFiberSpan
