import BisimplicialCommaZeroPointCalibration
import BisimplicialCommaChosenFiberSpan
import OrdinarySegalEndpointDescentFiber

/-!
# The original ordered endpoint pair in the reconstruction square

The comma object uses the actual zero outer row of pointResolution.
Its reconstructed point is the diagonal of that same natural transformation.
The pointed comparison therefore keeps the original ordered endpoints.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerNativeBisimplicialHorizontalMapping (BiSSet)
open DaggerNativeBisimplicialDiagonal (diagonalFunctor)
open DaggerNativeSimplicialReplacement (replacement)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalEndpointPointCalibration

open OrdinaryCSSLocalization (Space)
open OrdinarySegalResolutionMappingFibers (endpointResolution pointResolution)
open SimplicialReplacementChosenHomotopyFiber (pointBi pointDiagonalIso)
open BisimplicialCommaZeroPointCalibration (outerConstantPoint zeroTo)
open BisimplicialCommaDiagonalReconstruction
open ChosenHomotopyFiberComparison (chosenFiber)

noncomputable section

/-- Every point from the constant zero simplex is its actual outer-degeneracy extension. -/
theorem outerConstantPoint_eq {B : BiSSet.{0}} (η : pointBi.{0} ⟶ B) :
    outerConstantPoint B (η.app (op ⦋0⦌)) = η := by
  apply NatTrans.ext
  funext q
  have h := η.naturality (zeroTo q)
  change 𝟙 (Δ[0] : SSet.{0}) ≫ η.app q =
    η.app (op ⦋0⦌) ≫ B.map (zeroTo q) at h
  change η.app (op ⦋0⦌) ≫ B.map (zeroTo q) = η.app q
  simpa only [Category.id_comp] using h.symm

/-- The comma arrow is exactly the original ordered endpoint resolution. -/
def endpointArrow (W : Space) : Arrow BiSSet.{0} := Arrow.mk (endpointResolution W)

/-- Insert the actual ordered pair from the zero outer row into the whole parameter bar. -/
def parameterPoint (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    (Δ[0] : SSet.{0}) ⟶
      DaggerBisimplicialDiagonal.diag (replacement (parameterDiagram (endpointArrow W))) :=
  BisimplicialCommaParameterProjection.zeroSimplexParameterPoint (endpointArrow W)
    (op ⦋0⦌) ((pointResolution W x y).app (op ⦋0⦌))

/-- Reconstruction retains precisely the original ordered endpoint-pair point. -/
theorem parameterPoint_reconstruction (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    parameterPoint W x y ≫ diagonalFunctor.map (baseReconstruction (endpointArrow W)) =
      pointDiagonalIso.inv ≫ diagonalFunctor.map (pointResolution W x y) := by
  have h := BisimplicialCommaZeroPointCalibration.zeroPoint_baseReconstruction
    (endpointArrow W) ((pointResolution W x y).app (op ⦋0⦌))
  change parameterPoint W x y ≫
      diagonalFunctor.map (baseReconstruction (endpointArrow W)) =
    pointDiagonalIso.inv ≫ diagonalFunctor.map
      (outerConstantPoint (endpointArrow W).right
        ((pointResolution W x y).app (op ⦋0⦌))) at h
  rw [outerConstantPoint_eq] at h
  exact h

/-- The actual chosen-fiber comparison lands at the unchanged ordered endpoint point. -/
def originalFiberComparison (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    chosenFiber (BisimplicialCommaChosenFiberSpan.barArrow (endpointArrow W))
        (parameterPoint W x y) ⟶
      chosenFiber (diagonalFunctor.map (endpointResolution W))
        (pointDiagonalIso.inv ≫ diagonalFunctor.map (pointResolution W x y)) :=
  ChosenHomotopyFiberFunctor.chosenMap _ _
    (diagonalFunctor.map (totalReconstruction (endpointArrow W)))
    (diagonalFunctor.map (baseReconstruction (endpointArrow W)))
    (BisimplicialCommaChosenFiberSpan.original_square (endpointArrow W))
    (parameterPoint W x y) _ (parameterPoint_reconstruction W x y)

/-- The pointed reconstruction is weak at the exact original ordered pair. -/
theorem originalFiberComparison_weak (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    WeakEquivalence (originalFiberComparison W x y) := by
  have : WeakEquivalence (diagonalFunctor.map (totalReconstruction (endpointArrow W))) :=
    totalReconstruction_diagonal_weak (endpointArrow W)
  have : WeakEquivalence (diagonalFunctor.map (baseReconstruction (endpointArrow W))) :=
    baseReconstruction_diagonal_weak (endpointArrow W)
  exact DiagonalRecognition.chosenMap_weak_of_weak_square _ _ _ _ _ _ _ _

#print axioms outerConstantPoint_eq
#print axioms parameterPoint_reconstruction
#print axioms originalFiberComparison_weak

end

end DaggerModels.PartII.OrdinarySegalEndpointPointCalibration
