import OrdinarySegalWalkingFullFaithfulnessAudit
import OrdinaryWalkingCoherentEssentialSurjectivity

/-!
# The original walking comparison and its concrete object witnesses

The exact constant walking section is fully faithful on ordered mapping
fibers of the original ordinary JT input. Every literal target object
also has a whole coherent walking arrow to a constant-section object.
Neither the full completion theorem nor original Theorem C is asserted.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalWalkingComparisonAudit

noncomputable section

private abbrev J := GroupoidSimplex.parameter.obj ⦋1⦌
private abbrev input (W : SegalLocalizers.ReverseDaggerSpace.{0}) :=
  RawOrdinaryJTQuillenTranspose.input W

/-- At the unchanged original JT input, every literal walking-cotensor
object is coherently connected to a literal constant-section object. -/
theorem originalInput_coherent_object_witness
    (W : SegalLocalizers.ReverseDaggerSpace.{0})
    (z : ((OrdinarySegalHorizontalCotensor.cotensor J (input W)).obj
      (op ⦋0⦌)).obj (op ⦋0⦌)) :
    ∃ x : ((input W).obj (op ⦋0⦌)).obj (op ⦋0⦌),
      ∃ H : J ⟶ (OrdinarySegalHorizontalCotensor.cotensor J (input W)).flip.obj
          (op ⦋0⦌),
        SSet.yonedaEquiv
            (X := (OrdinarySegalHorizontalCotensor.cotensor J (input W)).flip.obj
              (op ⦋0⦌)) (n := ⦋0⦌)
            (JTParameterContraction.parameterVertex ⦋1⦌ 0 ≫ H) = z ∧
          SSet.yonedaEquiv
            (X := (OrdinarySegalHorizontalCotensor.cotensor J (input W)).flip.obj
              (op ⦋0⦌)) (n := ⦋0⦌)
            (JTParameterContraction.parameterVertex ⦋1⦌ 1 ≫ H) =
            ((OrdinarySegalHorizontalCotensorPoint.constantSection J (input W)).app
              (op ⦋0⦌)).app (op ⦋0⦌) x :=
  OrdinaryWalkingCoherentEssentialSurjectivity.coherent_object_witness (input W) z

#print axioms originalInput_coherent_object_witness
#print axioms
  OrdinarySegalWalkingFullFaithfulnessAudit.originalInput_constantWalking_mappingMap_weak
#print axioms OrdinaryWalkingCoherentEssentialSurjectivity.coherent_object_witness
#print axioms OrdinaryWalkingCoherentEssentialSurjectivity.endpoint_one_constant
#print axioms OrdinaryWalkingCoherentEssentialSurjectivity.endpoint_zero
#print axioms OrdinaryWalkingCoherentVertexCalibration.simplexUnit_vertex
#print axioms OrdinarySegalCotensorConstantObject.objectMap_constant
#print axioms JTTheoremCFromOriginalRawOrderedUnit.statement_of_originalRawOrderedUnit

end
end DaggerModels.PartII.OrdinarySegalWalkingComparisonAudit
