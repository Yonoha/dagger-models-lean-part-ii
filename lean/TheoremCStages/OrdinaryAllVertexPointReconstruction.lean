import OrdinarySegalAllVertexDiagonalCalibration
import OrdinarySegalAllVertexDescent
import OrdinaryAllVertexStrictFibreMap
import OrdinarySegalEndpointPointCalibration
import BisimplicialCommaZeroTotalReconstruction

/-!
# Original complete vertex tuples in the comma reconstruction

Every finite tuple is kept as its actual point of the complete vertex mapping
space. The zero comma fiber uses the original constant section. Its total
reconstruction and point reconstruction are the corrected unit and the exact
same tuple, rather than a selected endpoint pair.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerNativeBisimplicialHorizontalMapping (BiSSet)
open DaggerNativeBisimplicialDiagonal (diagonalFunctor)
open DaggerSimplicialReplacementChosenFiber (diagonalInclusion)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryAllVertexPointReconstruction

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalVertexTupleFibres (vertices vertexMap)
open OrdinarySegalAllVertexDescent (vertexArrow)
open OrdinarySegalAllVertexDiagonal (vertexBaseDiagonalIso)
open OrdinarySegalAllVertexDiagonalCalibration (vertexBaseUnit)
open OrdinarySegalResolutionMappingFibers (rowResolution rowUnit)
open BisimplicialBaseSimplexFibers (fiberDiagram)
open BisimplicialCommaParameterProjection (zeroSimplexIndex)
open SimplicialReplacementChosenHomotopyFiber (pointBi pointDiagonalIso)

noncomputable section

private abbrev zero : SimplexCategoryᵒᵖ := op ⦋0⦌
private abbrev P (W : Space) := OrdinarySegalVerticalPrecompletion.precompletion W

/-- The original full tuple point, natural in the unchanged outer parameter. -/
def pointResolution (W : Space) (n : ℕ)
    (b : (Δ[0] : SSet.{0}) ⟶ diagramMappingSpace (discrete.obj (vertices n)) W) :
    pointBi.{0} ⟶ (vertexArrow W n).right :=
  (Functor.const SimplexCategoryᵒᵖ).map b ≫ vertexBaseUnit W n

/-- Its actual zero outer row is the point used by the full comma category. -/
def zeroBoundary (W : Space) (n : ℕ)
    (b : (Δ[0] : SSet.{0}) ⟶ diagramMappingSpace (discrete.obj (vertices n)) W) :
    (Δ[0] : SSet.{0}) ⟶ (vertexArrow W n).right.obj zero :=
  (pointResolution W n b).app zero

/-- Enter the literal zero comma fiber through the original full-tuple map. -/
def zeroFiberComparison (W : Space) (n : ℕ)
    (b : (Δ[0] : SSet.{0}) ⟶ diagramMappingSpace (discrete.obj (vertices n)) W) :
    pullback (vertexMap W n) b ⟶
      (fiberDiagram (vertexArrow W n)).obj
        (zeroSimplexIndex (vertexArrow W n) zero (zeroBoundary W n b)) :=
  OrdinaryAllVertexStrictFibreMap.tupleMap
    ((OrdinarySegalPrecompletion.resolutionUnit W).app zero) n b

/-- The original zero fiber retains the actual source projection and zero-row unit. -/
theorem zeroFiberComparison_fst (W : Space) (n : ℕ)
    (b : (Δ[0] : SSet.{0}) ⟶ diagramMappingSpace (discrete.obj (vertices n)) W) :
    zeroFiberComparison W n b ≫
        pullback.fst ((vertexArrow W n).hom.app zero) (zeroBoundary W n b) =
      pullback.fst (vertexMap W n) b ≫ (rowUnit W n).app zero := by
  unfold zeroFiberComparison OrdinaryAllVertexStrictFibreMap.tupleMap
  exact DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_fst _ _ _ _ _ _ _ _

/-- The actual complete tuple, inserted into the original parameter bar. -/
def parameterPoint (W : Space) (n : ℕ)
    (b : (Δ[0] : SSet.{0}) ⟶ diagramMappingSpace (discrete.obj (vertices n)) W) :=
  BisimplicialCommaParameterProjection.zeroSimplexParameterPoint
    (vertexArrow W n) zero (zeroBoundary W n b)

/-- Its point in the diagonal base is the diagonal of the same outer natural point. -/
def diagonalPoint (W : Space) (n : ℕ)
    (b : (Δ[0] : SSet.{0}) ⟶ diagramMappingSpace (discrete.obj (vertices n)) W) :
    (Δ[0] : SSet.{0}) ⟶ diagonalFunctor.obj (vertexArrow W n).right :=
  pointDiagonalIso.inv ≫ diagonalFunctor.map (pointResolution W n b)

/-- Reconstruction preserves the original full tuple point, in all dimensions. -/
theorem parameterPoint_reconstruction (W : Space) (n : ℕ)
    (b : (Δ[0] : SSet.{0}) ⟶ diagramMappingSpace (discrete.obj (vertices n)) W) :
    parameterPoint W n b ≫ diagonalFunctor.map
        (BisimplicialCommaDiagonalReconstruction.baseReconstruction (vertexArrow W n)) =
      diagonalPoint W n b := by
  have h := BisimplicialCommaZeroPointCalibration.zeroPoint_baseReconstruction
    (vertexArrow W n) (zeroBoundary W n b)
  change parameterPoint W n b ≫ diagonalFunctor.map
      (BisimplicialCommaDiagonalReconstruction.baseReconstruction (vertexArrow W n)) =
    pointDiagonalIso.inv ≫ diagonalFunctor.map
      (BisimplicialCommaZeroPointCalibration.outerConstantPoint
        (vertexArrow W n).right ((pointResolution W n b).app zero)) at h
  rw [OrdinarySegalEndpointPointCalibration.outerConstantPoint_eq] at h
  exact h

/-- The diagonal tuple is exactly the tuple mapped by the corrected unit. -/
theorem diagonalPoint_unit (W : Space) (n : ℕ)
    (b : (Δ[0] : SSet.{0}) ⟶ diagramMappingSpace (discrete.obj (vertices n)) W) :
    b ≫ diagramMappingPostcomp (discrete.obj (vertices n))
        (OrdinarySegalVerticalPrecompletion.unit W) ≫
        (vertexBaseDiagonalIso W n).hom = diagonalPoint W n b := by
  have h := OrdinarySegalAllVertexDiagonalCalibration.vertexBaseUnit_diagonal W n
  have hc : b ≫
      (OrdinarySegalVerticalPrecompletionFiberComparison.constantDiagonalIso
        (diagramMappingSpace (discrete.obj (vertices n)) W)).inv =
      pointDiagonalIso.inv ≫
        diagonalFunctor.map ((Functor.const SimplexCategoryᵒᵖ).map b) := by
    apply NatTrans.ext
    funext q x
    rfl
  calc
    _ = b ≫
        (OrdinarySegalVerticalPrecompletionFiberComparison.constantDiagonalIso
          (diagramMappingSpace (discrete.obj (vertices n)) W)).inv ≫
        diagonalFunctor.map (vertexBaseUnit W n) := by
      simpa only [Category.assoc] using congrArg (b ≫ ·) h
    _ = _ := by
      rw [← Category.assoc, hc, Category.assoc, ← diagonalFunctor.map_comp]
      rfl

private def globalTotal (W : Space) (n : ℕ)
    (b : (Δ[0] : SSet.{0}) ⟶ diagramMappingSpace (discrete.obj (vertices n)) W) :
    BisimplicialRowBarZeroAugmentation.constantBi (pullback (vertexMap W n) b) ⟶
      rowResolution W n :=
  (Functor.const SimplexCategoryᵒᵖ).map (pullback.fst (vertexMap W n) b) ≫ rowUnit W n

/-- The entire reconstructed total coordinate is the unchanged corrected unit. -/
theorem zeroFiber_totalReconstruction_unit (W : Space) (n : ℕ)
    (b : (Δ[0] : SSet.{0}) ⟶ diagramMappingSpace (discrete.obj (vertices n)) W) :
    (zeroFiberComparison W n b ≫
        diagonalInclusion (fiberDiagram (vertexArrow W n))
          (zeroSimplexIndex (vertexArrow W n) zero (zeroBoundary W n b))) ≫
      diagonalFunctor.map
        (BisimplicialCommaDiagonalReconstruction.totalReconstruction (vertexArrow W n)) =
    pullback.fst (vertexMap W n) b ≫
      (OrdinarySegalVerticalPrecompletion.unit W).app (op ⦋n⦌) := by
  have h := BisimplicialCommaZeroTotalReconstruction.zeroFiber_totalReconstruction
    (vertexArrow W n) (zeroBoundary W n b) (zeroFiberComparison W n b)
  have hg : (globalTotal W n b).app zero =
      zeroFiberComparison W n b ≫
        pullback.fst ((vertexArrow W n).hom.app zero) (zeroBoundary W n b) :=
    (zeroFiberComparison_fst W n b).symm
  have he : BisimplicialRowBarZeroAugmentation.outerConstantValue
      (rowResolution W n)
      (zeroFiberComparison W n b ≫
        pullback.fst ((vertexArrow W n).hom.app zero) (zeroBoundary W n b)) =
      globalTotal W n b := by
    rw [← hg]
    exact BisimplicialCommaZeroTotalReconstruction.outerConstantValue_eq _
  have h' := h.trans (congrArg
    (fun m ↦ (BisimplicialRowBarZeroAugmentation.constantDiagonalIso
      (pullback (vertexMap W n) b)).inv ≫ diagonalFunctor.map m) he)
  calc
    _ = (BisimplicialRowBarZeroAugmentation.constantDiagonalIso
        (pullback (vertexMap W n) b)).inv ≫ diagonalFunctor.map (globalTotal W n b) := h'
    _ = _ := by
      apply NatTrans.ext
      funext q x
      exact congrFun (OrdinarySegalAllVertexPrecompletionFibres.rowUnit_diagonal W n q) _

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- The actual zero-row full-tuple comparison is weak before reconstruction. -/
theorem zeroFiberComparison_weak (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) (n : ℕ)
    (b : (Δ[0] : SSet.{0}) ⟶ diagramMappingSpace (discrete.obj (vertices n)) W) :
    WeakEquivalence (zeroFiberComparison W n b) :=
  OrdinaryAllVertexStrictFibreMap.constantSection_tupleMap_weak W hSegal ⦋0⦌ n b

#print axioms zeroFiberComparison_fst
#print axioms parameterPoint_reconstruction
#print axioms diagonalPoint_unit
#print axioms zeroFiber_totalReconstruction_unit
#print axioms zeroFiberComparison_weak

end

end DaggerModels.PartII.OrdinaryAllVertexPointReconstruction
