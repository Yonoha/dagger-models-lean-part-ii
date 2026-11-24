import OrdinaryGroupoidSimplexCotensorHomotopyInverse
import OrdinarySegalWalkingComparisonAudit

/-!
# Original-input audit of the whole groupoid-simplex cotensor homotopies

The source is the unchanged ordinary JT input. For every original parameter
simplex and selected vertex, the exact constant section has an evaluation
retraction and a whole coherent homotopy for the opposite composite.
The original ordered-fiber weakness and Theorem C are still not asserted.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.OrdinaryGroupoidSimplexCotensorHomotopyAudit

open OrdinarySegalHorizontalCotensor (cotensor)
open OrdinarySegalHorizontalCotensorPoint (constantSection)
open OrdinarySegalCotensorPointEvaluation (evaluation)
open OrdinaryGroupoidSimplexCotensorHomotopyInverse (homotopy)

noncomputable section

private abbrev E (k : SimplexCategory) := GroupoidSimplex.parameter.obj k
private abbrev input (W : SegalLocalizers.ReverseDaggerSpace.{0}) :=
  RawOrdinaryJTQuillenTranspose.input W

/-- The whole homotopy and both original endpoints at the unchanged input,
for every groupoid-completed simplex rather than only `E[1]`. -/
theorem originalInput_homotopy_endpoints
    (W : SegalLocalizers.ReverseDaggerSpace.{0})
    (k : SimplexCategory) (j : Fin (k.len + 1)) :
    (constantSection (E k) (input W) ≫
        evaluation (E k) (input W) (JTParameterContraction.parameterVertex k j) =
      𝟙 (input W)) ∧
    (homotopy k j (input W) ≫
        evaluation (E ⦋1⦌) (cotensor (E k) (input W))
          (JTParameterContraction.parameterVertex ⦋1⦌ 0) =
      𝟙 (cotensor (E k) (input W))) ∧
    (homotopy k j (input W) ≫
        evaluation (E ⦋1⦌) (cotensor (E k) (input W))
          (JTParameterContraction.parameterVertex ⦋1⦌ 1) =
      evaluation (E k) (input W) (JTParameterContraction.parameterVertex k j) ≫
        constantSection (E k) (input W)) :=
  ⟨OrdinaryGroupoidSimplexCotensorHomotopyInverse.section_evaluation k j (input W),
    OrdinaryGroupoidSimplexCotensorHomotopyInverse.homotopy_zero k j (input W),
    OrdinaryGroupoidSimplexCotensorHomotopyInverse.homotopy_one k j (input W)⟩

#print axioms originalInput_homotopy_endpoints
#print axioms OrdinarySegalCotensorParameterHomotopy.homotopy_evaluation
#print axioms OrdinaryGroupoidSimplexCoherentContraction.slice_simplexUnit_vertex
#print axioms
  OrdinarySegalWalkingFullFaithfulnessAudit.originalInput_constantWalking_mappingMap_weak
#print axioms OrdinarySegalWalkingComparisonAudit.originalInput_coherent_object_witness
#print axioms JTTheoremCFromOriginalRawOrderedUnit.statement_of_originalRawOrderedUnit

end
end DaggerModels.PartII.OrdinaryGroupoidSimplexCotensorHomotopyAudit
