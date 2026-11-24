import BisimplicialCommaZeroTotalReconstruction
import OrdinarySegalVerticalPrecompletionFiberComparison

/-!
# The zero-row endpoint fiber and the corrected unit's total coordinate

The actual source mapping fiber enters the comma fiber at the original
zero-row endpoint simplex. Reconstructing its total coordinate applies
exactly the corrected vertical precompletion unit in horizontal degree one.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerNativeBisimplicialHorizontalMapping (BiSSet)
open DaggerNativeBisimplicialDiagonal (diagonalFunctor)
open DaggerSimplicialReplacementChosenFiber (diagonalInclusion)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalEndpointZeroTotalUnit

open OrdinaryCSSLocalization (Space)
open OrdinarySegalOrderedMappingFibres (endpointArrow endpointPoint mappingFiber)
open OrdinarySegalResolutionMappingFibers
open BisimplicialBaseSimplexFibers (fiberDiagram)
open BisimplicialCommaParameterProjection (zeroSimplexIndex)
open BisimplicialCommaZeroTotalReconstruction (outerConstantValue_eq)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev zero : SimplexCategoryᵒᵖ := op ⦋0⦌

private def endpointBiArrow (W : Space) : Arrow BiSSet.{0} :=
  Arrow.mk (endpointResolution W)

private def zeroBoundary (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    (Δ[0] : SSet.{0}) ⟶ (endpointBiArrow W).right.obj zero :=
  (pointResolution W x y).app zero

/-- The original strict ordered fiber enters the literal zero-row comma
fiber through the same pointwise pullback comparison. -/
def zeroFiberComparison (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    mappingFiber W x y ⟶
      (fiberDiagram (endpointBiArrow W)).obj
        (zeroSimplexIndex (endpointBiArrow W) zero (zeroBoundary W x y)) :=
  (constantFiberComparison W x y).app zero ≫
    (rowFiberIso W x y zero).hom

/-- Its total projection is precisely the original row-zero unit applied
to the original horizontal degree-one strict-fiber coordinate. -/
theorem zeroFiberComparison_fst (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    zeroFiberComparison W x y ≫
        pullback.fst ((endpointResolution W).app zero) (zeroBoundary W x y) =
      pullback.fst (endpointArrow W) (endpointPoint W x y) ≫
        (rowUnit W 1).app zero := by
  have h := congrArg (fun m ↦ m.app zero) (constantFiberComparison_fst W x y)
  change (constantFiberComparison W x y).app zero ≫
      (pullback.fst (endpointResolution W) (pointResolution W x y)).app zero =
    pullback.fst (endpointArrow W) (endpointPoint W x y) ≫
      (rowUnit W 1).app zero at h
  calc
    _ = (constantFiberComparison W x y).app zero ≫
          (pullback.fst (endpointResolution W) (pointResolution W x y)).app zero := by
      rw [zeroFiberComparison, Category.assoc]
      exact congrArg ((constantFiberComparison W x y).app zero ≫ ·)
        (PreservesPullback.iso_hom_fst
          ((evaluation SimplexCategoryᵒᵖ SSet.{0}).obj zero)
          (endpointResolution W) (pointResolution W x y))
    _ = _ := h

/-- The same zero-row comparison is weak by the checked groupoid-simplex
fully faithful result; the row pullback identification is an isomorphism. -/
theorem zeroFiberComparison_weak (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    WeakEquivalence (zeroFiberComparison W x y) := by
  haveI : WeakEquivalence ((constantFiberComparison W x y).app zero) :=
    rowComparison_weak W hSegal x y zero
  unfold zeroFiberComparison
  infer_instance

/-- The full natural total map whose zero component is the original
source projection followed by the original resolution unit. -/
private def globalTotal (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    BisimplicialRowBarZeroAugmentation.constantBi (mappingFiber W x y) ⟶
      rowResolution W 1 :=
  (Functor.const SimplexCategoryᵒᵖ).map
      (pullback.fst (endpointArrow W) (endpointPoint W x y)) ≫
    rowUnit W 1

/-- Naturality of the original whole constant-section comparison says
its zero component determines every outer degeneracy of its total map. -/
private theorem outerConstantValue_zeroFiberComparison (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    BisimplicialRowBarZeroAugmentation.outerConstantValue
        (rowResolution W 1)
        (zeroFiberComparison W x y ≫
          pullback.fst ((endpointResolution W).app zero) (zeroBoundary W x y)) =
      globalTotal W x y := by
  have h : (globalTotal W x y).app zero =
      zeroFiberComparison W x y ≫
        pullback.fst ((endpointResolution W).app zero) (zeroBoundary W x y) := by
    change pullback.fst (endpointArrow W) (endpointPoint W x y) ≫
      (rowUnit W 1).app zero = _
    exact (zeroFiberComparison_fst W x y).symm
  rw [← h]
  exact outerConstantValue_eq (globalTotal W x y)

/-- On the original whole source fiber, the reconstructed total map is
the literal corrected vertical precompletion unit in degree one. -/
theorem zeroFiber_totalReconstruction_unit (W : Space)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    (zeroFiberComparison W x y ≫
        diagonalInclusion (fiberDiagram (endpointBiArrow W))
          (zeroSimplexIndex (endpointBiArrow W) zero (zeroBoundary W x y))) ≫
      diagonalFunctor.map
        (BisimplicialCommaDiagonalReconstruction.totalReconstruction
          (endpointBiArrow W)) =
    pullback.fst (endpointArrow W) (endpointPoint W x y) ≫
      (OrdinarySegalVerticalPrecompletion.unit W).app (op ⦋1⦌) := by
  have h := BisimplicialCommaZeroTotalReconstruction.zeroFiber_totalReconstruction
    (endpointBiArrow W) (zeroBoundary W x y) (zeroFiberComparison W x y)
  have heq := outerConstantValue_zeroFiberComparison W x y
  have h' := h.trans (congrArg
    (fun m ↦ (BisimplicialRowBarZeroAugmentation.constantDiagonalIso
      (mappingFiber W x y)).inv ≫ diagonalFunctor.map m) heq)
  calc
    _ = (BisimplicialRowBarZeroAugmentation.constantDiagonalIso
          (mappingFiber W x y)).inv ≫
        diagonalFunctor.map (globalTotal W x y) := h'
    _ = _ := by
      apply NatTrans.ext
      funext r z
      change ((rowUnit W 1).app r).app r
          ((pullback.fst (endpointArrow W) (endpointPoint W x y)).app r z) =
        ((OrdinarySegalVerticalPrecompletion.unit W).app (op ⦋1⦌)).app r
          ((pullback.fst (endpointArrow W) (endpointPoint W x y)).app r z)
      have hu : ((rowUnit W 1).app r).app r =
          ((OrdinarySegalVerticalPrecompletion.unit W).app (op ⦋1⦌)).app r :=
        (OrdinarySegalVerticalPrecompletion.unit_app_app W (op ⦋1⦌) r).symm
      exact congrFun hu _

#print axioms zeroFiberComparison
#print axioms zeroFiberComparison_fst
#print axioms zeroFiberComparison_weak
#print axioms zeroFiber_totalReconstruction_unit

end

end DaggerModels.PartII.OrdinarySegalEndpointZeroTotalUnit
