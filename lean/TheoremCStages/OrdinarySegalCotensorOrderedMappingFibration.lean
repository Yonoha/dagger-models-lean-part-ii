import OrdinarySegalCotensorRelativeEndpointFibration
import OrdinarySegalOrderedMappingMaps
import KanFibrationCornerFibre

/-!
# Parameter restrictions on the exact ordered mapping fibers

The checked relative endpoint comparison is the literal Kan corner for
the actual cotensor restriction. Its base change is the original ordered
mapping map, at the original vertices and their specified images.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalCotensorOrderedMappingFibration

open OrdinaryCSSLocalization (Space)
open OrdinarySegalHorizontalCotensor (cotensor pre)
open OrdinarySegalOrderedMappingFibres
open OrdinarySegalOrderedMappingMaps

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- A monomorphic parameter restriction induces the actual Kan fibration
on each original ordered mapping fiber. No Segal condition is required. -/
theorem mappingMap_fibration {K L : SSet.{0}} (f : K ⟶ L) [Mono f]
    (W : Space) [IsFibrant W]
    (x y : ((cotensor L W).obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    Fibration (mappingMap (pre f W) x y) := by
  have : Fibration (KanFibrationCornerFibre.corner
      (endpointArrow (cotensor L W)) (endpointArrow (cotensor K W))
      ((pre f W).app (op ⦋1⦌)) (endpointMap (pre f W))
      (endpoint_naturality (pre f W))) :=
    OrdinarySegalCotensorRelativeEndpointFibration.relativeEndpoint_fibration f W
  exact KanFibrationCornerFibre.fibreMap_fibration
    (endpointArrow (cotensor L W)) (endpointArrow (cotensor K W))
    ((pre f W).app (op ⦋1⦌)) (endpointMap (pre f W))
    (endpoint_naturality (pre f W)) (endpointPoint (cotensor L W) x y)
    (endpointPoint (cotensor K W)
      (((pre f W).app (op ⦋0⦌)).app (op ⦋0⦌) x)
      (((pre f W).app (op ⦋0⦌)).app (op ⦋0⦌) y))
    (point_naturality (pre f W) x y)

#print axioms mappingMap_fibration

end
end DaggerModels.PartII.OrdinarySegalCotensorOrderedMappingFibration
