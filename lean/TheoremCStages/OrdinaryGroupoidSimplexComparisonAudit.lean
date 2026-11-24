import OrdinaryGroupoidSimplexCotensorHomotopyAudit
import OrdinaryGroupoidSimplexCotensorTransitionHomotopy
import OrdinaryGroupoidSimplexCotensorObjectWitness
import OrdinaryGroupoidSimplexCotensorConstantHomotopy
import OrdinarySegalCoherentLeftOuterHorn
import OrdinarySegalCoherentOuterHornRow

/-!
# Original-input groupoid-simplex comparison audit

The original ordinary JT input retains every groupoid parameter, simplex
operator, selected vertex, and literal cotensor object. The checked whole
homotopies give the actual transition inverse composites and coherent object
witnesses. Neither arbitrary-object Dwyer–Kan recognition, completion, the
original raw ordered-fiber weakness, nor Theorem C is asserted.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.OrdinaryGroupoidSimplexComparisonAudit

open OrdinarySegalHorizontalCotensor (cotensor)
open OrdinarySegalHorizontalCotensorPoint (constantSection)
open OrdinarySegalCotensorPointEvaluation (evaluation)
open OrdinaryGroupoidSimplexCotensorTransitionHomotopy (transition inverse)

noncomputable section

private abbrev E (k : SimplexCategory) := GroupoidSimplex.parameter.obj k
private abbrev input (W : SegalLocalizers.ReverseDaggerSpace.{0}) :=
  RawOrdinaryJTQuillenTranspose.input W

/-- The actual inverse composites at the unchanged original JT input
retain the image vertex of every original simplex operator. -/
theorem originalInput_transition_inverse_composites
    (W : SegalLocalizers.ReverseDaggerSpace.{0})
    {n m : SimplexCategory} (θ : n ⟶ m) (j : Fin (n.len + 1)) :
    (transition θ (input W) ≫ inverse θ j (input W) =
      evaluation (E m) (input W)
        (JTParameterContraction.parameterVertex m (θ.toOrderHom j)) ≫
        constantSection (E m) (input W)) ∧
    (inverse θ j (input W) ≫ transition θ (input W) =
      evaluation (E n) (input W) (JTParameterContraction.parameterVertex n j) ≫
        constantSection (E n) (input W)) :=
  ⟨OrdinaryGroupoidSimplexCotensorTransitionHomotopy.transition_inverse_left θ j (input W),
    OrdinaryGroupoidSimplexCotensorTransitionHomotopy.transition_inverse_right θ j (input W)⟩

/-- Every literal object of every original groupoid-simplex cotensor
has the original coherent walking witness to a constant-section object. -/
theorem originalInput_coherent_object_witness
    (W : SegalLocalizers.ReverseDaggerSpace.{0})
    (k : SimplexCategory) (j : Fin (k.len + 1))
    (z : ((cotensor (E k) (input W)).obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    ∃ x : ((input W).obj (op ⦋0⦌)).obj (op ⦋0⦌),
      ∃ H : E ⦋1⦌ ⟶ (cotensor (E k) (input W)).flip.obj (op ⦋0⦌),
        SSet.yonedaEquiv
            (X := (cotensor (E k) (input W)).flip.obj (op ⦋0⦌)) (n := ⦋0⦌)
            (JTParameterContraction.parameterVertex ⦋1⦌ 0 ≫ H) = z ∧
          SSet.yonedaEquiv
            (X := (cotensor (E k) (input W)).flip.obj (op ⦋0⦌)) (n := ⦋0⦌)
            (JTParameterContraction.parameterVertex ⦋1⦌ 1 ≫ H) =
            ((constantSection (E k) (input W)).app (op ⦋0⦌)).app (op ⦋0⦌) x :=
  OrdinaryGroupoidSimplexCotensorObjectWitness.coherent_object_witness k j (input W) z

#print axioms originalInput_transition_inverse_composites
#print axioms originalInput_coherent_object_witness
#print axioms OrdinaryGroupoidSimplexCotensorHomotopyAudit.originalInput_homotopy_endpoints
#print axioms OrdinaryGroupoidSimplexCotensorConstantHomotopy.constantSection_homotopy
#print axioms OrdinaryGroupoidSimplexCotensorTransitionHomotopy.left_homotopy_zero
#print axioms OrdinaryGroupoidSimplexCotensorTransitionHomotopy.left_homotopy_one
#print axioms OrdinaryGroupoidSimplexCotensorTransitionHomotopy.right_homotopy_zero
#print axioms OrdinaryGroupoidSimplexCotensorTransitionHomotopy.right_homotopy_one
#print axioms OrdinarySegalCoherentLeftOuterHorn.fixedRestriction_trivialFibration
#print axioms OrdinarySegalCoherentOuterHornRow.rowLeftHorn_first
#print axioms OrdinarySegalCoherentOuterHornRow.rowLeftHorn_second
#print axioms JTTheoremCFromOriginalRawOrderedUnit.statement_of_originalRawOrderedUnit

end
end DaggerModels.PartII.OrdinaryGroupoidSimplexComparisonAudit
