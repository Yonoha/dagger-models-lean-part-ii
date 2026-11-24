import OrdinaryGroupoidSimplexCotensorHomotopyInverse
import OrdinarySegalCotensorObjectEvaluation

/-!
# Literal coherent object witnesses for every groupoid-simplex cotensor

The whole checked homotopy gives an actual original `E[1]` arrow from each
literal cotensor object to the constant section of its value at any selected
parameter vertex. Both object endpoints use the original parameter vertices.
No identification with all equivalences of a homotopy category is asserted.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.OrdinaryGroupoidSimplexCotensorObjectWitness

open OrdinaryCSSLocalization (Space)
open OrdinarySegalHorizontalCotensor (cotensor)
open OrdinarySegalHorizontalCotensorPoint (constantSection)
open OrdinarySegalCotensorPointEvaluation (evaluation)
open OrdinaryGroupoidSimplexCotensorHomotopyInverse (homotopy)
open OrdinaryWalkingCoherentObject (objectMap)

noncomputable section

private abbrev E (k : SimplexCategory) : SSet.{0} :=
  GroupoidSimplex.parameter.obj k

/-- Every original cotensor object has a whole coherent arrow to the
literal constant section at its specified parameter vertex. -/
theorem coherent_object_witness (k : SimplexCategory) (j : Fin (k.len + 1))
    (W : Space) (z : ((cotensor (E k) W).obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    ∃ x : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌),
      ∃ H : E ⦋1⦌ ⟶ (cotensor (E k) W).flip.obj (op ⦋0⦌),
        SSet.yonedaEquiv (X := (cotensor (E k) W).flip.obj (op ⦋0⦌)) (n := ⦋0⦌)
            (JTParameterContraction.parameterVertex ⦋1⦌ 0 ≫ H) = z ∧
          SSet.yonedaEquiv (X := (cotensor (E k) W).flip.obj (op ⦋0⦌)) (n := ⦋0⦌)
            (JTParameterContraction.parameterVertex ⦋1⦌ 1 ≫ H) =
            ((constantSection (E k) W).app (op ⦋0⦌)).app (op ⦋0⦌) x := by
  let C := cotensor (E k) W
  let t := ((homotopy k j W).app (op ⦋0⦌)).app (op ⦋0⦌) z
  let x := ((evaluation (E k) W (JTParameterContraction.parameterVertex k j)).app
    (op ⦋0⦌)).app (op ⦋0⦌) z
  refine ⟨x, objectMap (E ⦋1⦌) C t, ?_, ?_⟩
  · rw [OrdinarySegalCotensorObjectEvaluation.objectMap_evaluation]
    change (((homotopy k j W ≫
      evaluation (E ⦋1⦌) C (JTParameterContraction.parameterVertex ⦋1⦌ 0)).app
        (op ⦋0⦌)).app (op ⦋0⦌)) z = z
    rw [OrdinaryGroupoidSimplexCotensorHomotopyInverse.homotopy_zero]
    rfl
  · rw [OrdinarySegalCotensorObjectEvaluation.objectMap_evaluation]
    change (((homotopy k j W ≫
      evaluation (E ⦋1⦌) C (JTParameterContraction.parameterVertex ⦋1⦌ 1)).app
        (op ⦋0⦌)).app (op ⦋0⦌)) z = _
    rw [OrdinaryGroupoidSimplexCotensorHomotopyInverse.homotopy_one]
    rfl

#print axioms coherent_object_witness

end
end DaggerModels.PartII.OrdinaryGroupoidSimplexCotensorObjectWitness
