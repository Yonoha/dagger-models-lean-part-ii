import OrdinaryWalkingCoherentObjectEndpoints
import OrdinarySegalCotensorConstantObject

/-!
# A coherent walking arrow to an actual constant cotensor object

Every literal object of the cotensor by the original walking groupoid
is joined to a literal constant-section object by a whole coherent
walking arrow. This is the explicit object witness needed for essential
surjectivity; it makes no DK, completeness, or weak-equivalence claim.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.OrdinaryWalkingCoherentEssentialSurjectivity

open OrdinaryCSSLocalization (Space)
open OrdinarySegalHorizontalCotensor (cotensor)
open OrdinarySegalHorizontalCotensorPoint (constantSection)
open OrdinaryWalkingCoherentObject (objectIso objectMap objectArrow)
open OrdinaryWalkingCoherentObjectEndpoints
  (endpoint endpoint_zero_objectMap endpoint_one_objectMap)

noncomputable section

private abbrev E : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌

private theorem objectMap_injective (W : Space) :
    Function.Injective (objectMap E W) := by
  intro x y h
  change ((objectIso E W).hom.app (op ⦋0⦌)) x =
    ((objectIso E W).hom.app (op ⦋0⦌)) y at h
  haveI : IsIso ((objectIso E W).hom.app (op ⦋0⦌)) := inferInstance
  exact ((isIso_iff_bijective _).mp inferInstance).1 h

/-- The same chosen parameter vertex gives the literal constant-section
object that is the second endpoint of the coherent arrow. -/
theorem endpoint_one_constant (W : Space)
    (z : ((cotensor E W).obj (op ⦋0⦌)).obj (op ⦋0⦌)) (j : Fin 2) :
    endpoint W z j 1 =
      ((constantSection E W).app (op ⦋0⦌)).app (op ⦋0⦌)
        (SSet.yonedaEquiv (X := W.flip.obj (op ⦋0⦌)) (n := ⦋0⦌)
          (JTParameterContraction.parameterVertex ⦋1⦌ j ≫ objectMap E W z)) := by
  apply objectMap_injective W
  rw [endpoint_one_objectMap,
    OrdinarySegalCotensorConstantObject.objectMap_constant]
  rw [OrdinaryWalkingCoherentVertexCalibration.constantAt_vertex,
    Equiv.symm_apply_apply, Category.assoc]

/-- The first endpoint is precisely the original cotensor object. -/
theorem endpoint_zero (W : Space)
    (z : ((cotensor E W).obj (op ⦋0⦌)).obj (op ⦋0⦌)) (j : Fin 2) :
    endpoint W z j 0 = z :=
  objectMap_injective W (endpoint_zero_objectMap W z j)

/-- Every literal cotensor object is connected to the constant section
by an arrow indexed by the actual entire walking groupoid parameter.
The two endpoints use its original specified vertices. -/
theorem coherent_object_witness (W : Space)
    (z : ((cotensor E W).obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    ∃ x : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌),
      ∃ H : E ⟶ (cotensor E W).flip.obj (op ⦋0⦌),
        SSet.yonedaEquiv (X := (cotensor E W).flip.obj (op ⦋0⦌)) (n := ⦋0⦌)
            (JTParameterContraction.parameterVertex ⦋1⦌ 0 ≫ H) = z ∧
          SSet.yonedaEquiv (X := (cotensor E W).flip.obj (op ⦋0⦌)) (n := ⦋0⦌)
            (JTParameterContraction.parameterVertex ⦋1⦌ 1 ≫ H) =
            ((constantSection E W).app (op ⦋0⦌)).app (op ⦋0⦌) x := by
  let x : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌) :=
    SSet.yonedaEquiv (X := W.flip.obj (op ⦋0⦌)) (n := ⦋0⦌)
      (JTParameterContraction.parameterVertex ⦋1⦌ 0 ≫ objectMap E W z)
  refine ⟨x, objectArrow W z 0, ?_, ?_⟩
  · exact endpoint_zero W z 0
  · exact endpoint_one_constant W z 0

#print axioms endpoint_one_constant
#print axioms endpoint_zero
#print axioms coherent_object_witness

end
end DaggerModels.PartII.OrdinaryWalkingCoherentEssentialSurjectivity
