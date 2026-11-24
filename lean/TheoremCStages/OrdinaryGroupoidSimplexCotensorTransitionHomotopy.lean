import OrdinarySegalCotensorEvaluationNaturality
import OrdinaryGroupoidSimplexCotensorHomotopyInverse
import OrdinarySegalPrecompletion
import DaggerModelsPartII.JTParameterBlocks

/-!
# Coherent inverses for the actual groupoid-simplex transition maps

Every simplex operator keeps its original groupoid-parameter map. Evaluation
at a selected source vertex followed by the constant section is a whole-map
inverse up to the checked `E[1]` homotopies. No Dwyer–Kan recognition or
completion theorem is asserted here.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.OrdinaryGroupoidSimplexCotensorTransitionHomotopy

open OrdinaryCSSLocalization (Space)
open OrdinarySegalHorizontalCotensor (cotensor pre)
open OrdinarySegalHorizontalCotensorPoint (constantSection)
open OrdinarySegalCotensorPointEvaluation (evaluation)

noncomputable section

private abbrev E (k : SimplexCategory) : SSet.{0} :=
  GroupoidSimplex.parameter.obj k

/-- The unchanged contravariant transition along the original simplex
operator `θ`, retaining the entire groupoid-completed parameter. -/
def transition {n m : SimplexCategory} (θ : n ⟶ m) (W : Space) :
    cotensor (E m) W ⟶ cotensor (E n) W :=
  pre (GroupoidSimplex.parameter.map θ) W

/-- Evaluate at the selected source vertex and then insert the constant
target parameter. The source vertex is retained as an explicit argument. -/
def inverse {n m : SimplexCategory} (_θ : n ⟶ m)
    (j : Fin (n.len + 1)) (W : Space) :
    cotensor (E n) W ⟶ cotensor (E m) W :=
  evaluation (E n) W (JTParameterContraction.parameterVertex n j) ≫
    constantSection (E m) W

/-- Evaluation after the actual transition uses exactly the image of
the selected vertex under the original simplex operator. -/
theorem transition_evaluation {n m : SimplexCategory} (θ : n ⟶ m)
    (j : Fin (n.len + 1)) (W : Space) :
    transition θ W ≫
        evaluation (E n) W (JTParameterContraction.parameterVertex n j) =
      evaluation (E m) W
        (JTParameterContraction.parameterVertex m (θ.toOrderHom j)) := by
  rw [transition, OrdinarySegalCotensorEvaluationNaturality.evaluation_pre,
    JTParameterBlocks.parameterVertex_map]

/-- The first composite is the original evaluation followed by its
constant section at the image vertex. -/
theorem transition_inverse_left {n m : SimplexCategory} (θ : n ⟶ m)
    (j : Fin (n.len + 1)) (W : Space) :
    transition θ W ≫ inverse θ j W =
      evaluation (E m) W
        (JTParameterContraction.parameterVertex m (θ.toOrderHom j)) ≫
        constantSection (E m) W := by
  rw [inverse, ← Category.assoc, transition_evaluation]

/-- The second composite is the original evaluation followed by its
constant section at the selected source vertex. -/
theorem transition_inverse_right {n m : SimplexCategory} (θ : n ⟶ m)
    (j : Fin (n.len + 1)) (W : Space) :
    inverse θ j W ≫ transition θ W =
      evaluation (E n) W (JTParameterContraction.parameterVertex n j) ≫
        constantSection (E n) W := by
  rw [inverse, Category.assoc, transition,
    OrdinarySegalPrecompletion.constantSection_pre]

/-- The time-zero endpoint on the target cotensor is its identity. -/
theorem left_homotopy_zero {n m : SimplexCategory} (θ : n ⟶ m)
    (j : Fin (n.len + 1)) (W : Space) :
    OrdinaryGroupoidSimplexCotensorHomotopyInverse.homotopy
        m (θ.toOrderHom j) W ≫
      evaluation (E ⦋1⦌) (cotensor (E m) W)
        (JTParameterContraction.parameterVertex ⦋1⦌ 0) =
      𝟙 (cotensor (E m) W) :=
  OrdinaryGroupoidSimplexCotensorHomotopyInverse.homotopy_zero
    m (θ.toOrderHom j) W

/-- The time-one endpoint on the target cotensor is the first composite. -/
theorem left_homotopy_one {n m : SimplexCategory} (θ : n ⟶ m)
    (j : Fin (n.len + 1)) (W : Space) :
    OrdinaryGroupoidSimplexCotensorHomotopyInverse.homotopy
        m (θ.toOrderHom j) W ≫
      evaluation (E ⦋1⦌) (cotensor (E m) W)
        (JTParameterContraction.parameterVertex ⦋1⦌ 1) =
      transition θ W ≫ inverse θ j W := by
  rw [OrdinaryGroupoidSimplexCotensorHomotopyInverse.homotopy_one,
    transition_inverse_left]

/-- The time-zero endpoint on the source cotensor is its identity. -/
theorem right_homotopy_zero {n m : SimplexCategory} (_θ : n ⟶ m)
    (j : Fin (n.len + 1)) (W : Space) :
    OrdinaryGroupoidSimplexCotensorHomotopyInverse.homotopy n j W ≫
      evaluation (E ⦋1⦌) (cotensor (E n) W)
        (JTParameterContraction.parameterVertex ⦋1⦌ 0) =
      𝟙 (cotensor (E n) W) :=
  OrdinaryGroupoidSimplexCotensorHomotopyInverse.homotopy_zero n j W

/-- The time-one endpoint on the source cotensor is the second composite. -/
theorem right_homotopy_one {n m : SimplexCategory} (θ : n ⟶ m)
    (j : Fin (n.len + 1)) (W : Space) :
    OrdinaryGroupoidSimplexCotensorHomotopyInverse.homotopy n j W ≫
      evaluation (E ⦋1⦌) (cotensor (E n) W)
        (JTParameterContraction.parameterVertex ⦋1⦌ 1) =
      inverse θ j W ≫ transition θ W := by
  rw [OrdinaryGroupoidSimplexCotensorHomotopyInverse.homotopy_one,
    transition_inverse_right]

#print axioms transition_evaluation
#print axioms transition_inverse_left
#print axioms transition_inverse_right
#print axioms left_homotopy_zero
#print axioms left_homotopy_one
#print axioms right_homotopy_zero
#print axioms right_homotopy_one

end
end DaggerModels.PartII.OrdinaryGroupoidSimplexCotensorTransitionHomotopy
