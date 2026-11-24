import OrdinarySegalCotensorRelativeEndpointFibration
import OrdinarySegalCotensorUnitEndpointDiagonal
import OrdinarySegalCotensorUnitHomotopyMono
import OrdinarySegalOrderedMappingMaps
import KanHomotopyMonomorphismSpecifiedFibre

/-!
# Weak diagonals of the original unit restriction on ordered mapping fibers

The total-row and endpoint-pair weak diagonals are transferred through the
literal relative endpoint fibration. The result is the weak strict diagonal
of the original ordered fiber map, retaining both actual image vertices.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalCotensorUnitMappingDiagonal

open OrdinaryCSSLocalization (Space)
open OrdinarySegalHorizontalCotensor (cotensor pre)
open OrdinarySegalOrderedMappingFibres
open OrdinarySegalOrderedMappingMaps

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev J := GroupoidSimplex.parameter.obj ⦋1⦌
private abbrev unit := JTCylinderCEComparison.simplexUnit.app ⦋1⦌

/-- The original walking-unit restriction is a homotopy monomorphism on
each literal ordered mapping fiber, at the original vertices and images. -/
theorem unit_mappingMap_diagonal_weak (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (x y : ((cotensor J W).obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    WeakEquivalence (KanHomotopyMonomorphism.diagonal (mappingMap (pre unit W) x y)) := by
  have : IsFibrant (cotensor J W) :=
    OrdinarySegalCotensorFibrant.cotensor_injectiveFibrant J W inferInstance
  have : IsFibrant (cotensor (Δ[1] : SSet.{0}) W) :=
    OrdinarySegalCotensorFibrant.cotensor_injectiveFibrant _ W inferInstance
  have : Fibration (endpointArrow (cotensor J W)) := endpointArrow_fibration _
  have : Fibration (endpointArrow (cotensor (Δ[1] : SSet.{0}) W)) :=
    endpointArrow_fibration _
  have : Mono unit := JTSimplexUnitKan.simplexUnit_mono ⦋1⦌
  have : WeakEquivalence (KanHomotopyMonomorphism.diagonal
      ((pre unit W).app (op ⦋1⦌))) :=
    OrdinarySegalCotensorUnitHomotopyMono.unitRow_diagonal_weak W hSegal ⦋1⦌
  have : WeakEquivalence (KanHomotopyMonomorphism.diagonal (endpointMap (pre unit W))) :=
    OrdinarySegalCotensorUnitEndpointDiagonal.unitRowPair_diagonal_weak W hSegal ⦋0⦌
  apply KanHomotopyMonomorphismSpecifiedFibre.fibreMap_diagonal_weak
    (endpointArrow (cotensor J W)) (endpointArrow (cotensor (Δ[1] : SSet.{0}) W))
    ((pre unit W).app (op ⦋1⦌)) (endpointMap (pre unit W))
    (endpoint_naturality (pre unit W)) (endpointPoint (cotensor J W) x y)
    (endpointPoint (cotensor (Δ[1] : SSet.{0}) W)
      (((pre unit W).app (op ⦋0⦌)).app (op ⦋0⦌) x)
      (((pre unit W).app (op ⦋0⦌)).app (op ⦋0⦌) y))
    (point_naturality (pre unit W) x y)
  exact OrdinarySegalCotensorRelativeEndpointFibration.relativeEndpoint_fibration unit W

#print axioms unit_mappingMap_diagonal_weak

end
end DaggerModels.PartII.OrdinarySegalCotensorUnitMappingDiagonal
