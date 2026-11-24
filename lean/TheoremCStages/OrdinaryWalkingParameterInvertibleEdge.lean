import DaggerModelsPartII.GroupoidSimplex
import DaggerModelsPartII.JTCylinderCEComparison
import NativeKanSourceOriginalCoreFactor
import OriginalOrdinaryKanCoreEdgeMaximality
import OriginalInnerHornFillers

/-!
# The original walking-parameter unit has an invertible image

The literal parameter `J[1]` is Kan. Hence the image of its original unit
edge under any map to a simplicial set lies in the exact ordinary core.
This gives the critical-edge fact used by the relative walking extension,
with no completeness or extension premise.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial
open DaggerOriginalInnerHornFillers DaggerOriginalOrdinaryKanCoreEdgeMembership
open DaggerOriginalOrdinaryKanCoreEdgeMaximality

namespace DaggerModels.PartII.OrdinaryWalkingParameterInvertibleEdge

noncomputable section

/-- Any image of the original unit edge from the actual walking parameter
is invertible in the original homotopy category of the target. -/
theorem simplexUnit_image_invertible (C : SSet.{0})
    (H : GroupoidSimplex.parameter.obj ⦋1⦌ ⟶ C) :
    edgeIsInvertible C
      (SSet.yonedaEquiv
        (JTCylinderCEComparison.simplexUnit.app ⦋1⦌ ≫ H)) := by
  letI : (GroupoidSimplex.parameter.obj ⦋1⦌).KanComplex :=
    GroupoidSimplex.parameter_kan ⦋1⦌
  have hmem := DaggerNativeKanSourceOriginalCoreFactor.kan_map_mem_core H
    (op ⦋1⦌)
    (SSet.yonedaEquiv (JTCylinderCEComparison.simplexUnit.app ⦋1⦌))
  have he := (mem_ordinaryCoreCandidate_one_iff C _).mp hmem
  rwa [SSet.yonedaEquiv_comp]

/-- The same conclusion with the inner-horn filler data carried by a
quasicategorical target in the relative walking construction. -/
theorem simplexUnit_image_invertible_of_inner (C : SSet.{0})
    (_hC : innerHornFillers C)
    (H : GroupoidSimplex.parameter.obj ⦋1⦌ ⟶ C) :
    edgeIsInvertible C
      (SSet.yonedaEquiv
        (JTCylinderCEComparison.simplexUnit.app ⦋1⦌ ≫ H)) :=
  simplexUnit_image_invertible C H

#print axioms simplexUnit_image_invertible
#print axioms simplexUnit_image_invertible_of_inner

end

end DaggerModels.PartII.OrdinaryWalkingParameterInvertibleEdge
