import OrdinaryWalkingCoherentObject
import OrdinaryWalkingCoherentVertexCalibration
import TopCatModelCategory.SSet.Monoidal

/-!
# Actual endpoints of the coherent walking arrow of a cotensor object

The row-zero right unitor and the closed tensor adjunction compare the
literal cotensor object map with evaluation of the coherent arrow at the
original parameter vertices. Both endpoint equations retain the entire
walking-parameter map.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial MonoidalCategory MonoidalClosed

namespace DaggerModels.PartII.OrdinaryWalkingCoherentObjectEndpoints

open OrdinaryCSSLocalization (Space)
open OrdinarySegalHorizontalCotensor (cotensor)
open OrdinarySegalCotensorMappingIso (rowIso)
open OrdinaryWalkingCoherentObject (objectMap objectArrow objectIso)
open OrdinaryWalkingCoherentCotensorArrow (arrow_first_tensor arrow_second_tensor)
open OrdinaryWalkingCoherentContraction (slice)

noncomputable section

private abbrev E : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌

private theorem objectMap_rowIso (K : SSet.{0}) (W : Space)
    (t : ((cotensor K W).obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    objectMap K W t =
      (SSet.stdSimplex.rightUnitor K).inv ≫
        uncurry (SSet.yonedaEquiv.symm
          ((rowIso K W (op ⦋0⦌)).hom.app (op ⦋0⦌) t)) := by
  rfl

/-- Evaluation at an original walking vertex, still as a literal
zero-simplex of the unchanged cotensor row. -/
def endpoint (W : Space)
    (z : ((cotensor E W).obj (op ⦋0⦌)).obj (op ⦋0⦌))
    (j i : Fin 2) :
    ((cotensor E W).obj (op ⦋0⦌)).obj (op ⦋0⦌) :=
  SSet.yonedaEquiv (X := (cotensor E W).flip.obj (op ⦋0⦌)) (n := ⦋0⦌)
    (JTParameterContraction.parameterVertex ⦋1⦌ i ≫ objectArrow W z j)

private theorem endpoint_objectMap (W : Space)
    (z : ((cotensor E W).obj (op ⦋0⦌)).obj (op ⦋0⦌))
    (j i : Fin 2) :
    objectMap E W (endpoint W z j i) =
      slice i ≫ uncurry
        (objectArrow W z j ≫ (rowIso E W (op ⦋0⦌)).hom) := by
  rw [objectMap_rowIso]
  have h :
      (rowIso E W (op ⦋0⦌)).hom.app (op ⦋0⦌) (endpoint W z j i) =
        SSet.yonedaEquiv
          (JTParameterContraction.parameterVertex ⦋1⦌ i ≫
            objectArrow W z j ≫ (rowIso E W (op ⦋0⦌)).hom) := by
    dsimp only [endpoint]
    rw [← SSet.yonedaEquiv_comp, Category.assoc]
  rw [h, Equiv.symm_apply_apply, uncurry_natural_left]
  rw [← Category.assoc, OrdinaryWalkingCoherentVertexCalibration.slice_vertex]

/-- The first endpoint represents exactly the original cotensor object. -/
theorem endpoint_zero_objectMap (W : Space)
    (z : ((cotensor E W).obj (op ⦋0⦌)).obj (op ⦋0⦌)) (j : Fin 2) :
    objectMap E W (endpoint W z j 0) = objectMap E W z := by
  rw [endpoint_objectMap]
  exact arrow_first_tensor W (op ⦋0⦌) (objectMap E W z) j

/-- The second endpoint represents the original parameter map made
constant at the specified groupoid vertex, followed by the same object. -/
theorem endpoint_one_objectMap (W : Space)
    (z : ((cotensor E W).obj (op ⦋0⦌)).obj (op ⦋0⦌)) (j : Fin 2) :
    objectMap E W (endpoint W z j 1) =
      JTParameterContraction.constantAt ⦋1⦌ j ≫ objectMap E W z := by
  rw [endpoint_objectMap]
  exact arrow_second_tensor W (op ⦋0⦌) (objectMap E W z) j

#print axioms endpoint_zero_objectMap
#print axioms endpoint_one_objectMap

end
end DaggerModels.PartII.OrdinaryWalkingCoherentObjectEndpoints
