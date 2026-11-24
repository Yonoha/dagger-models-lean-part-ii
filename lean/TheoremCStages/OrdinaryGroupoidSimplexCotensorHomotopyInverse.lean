import OrdinaryGroupoidSimplexCoherentContraction
import OrdinarySegalCotensorParameterHomotopy

/-!
# Whole coherent inverses for the original groupoid-simplex cotensors

The original constant section has an actual evaluation retraction at every
specified vertex. The opposite composite is joined to the identity by one whole
map with the original `E[1]` time parameter. Both endpoints use the original
parameter vertices. No Dwyer–Kan or completion conclusion is asserted here.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.OrdinaryGroupoidSimplexCotensorHomotopyInverse

open OrdinaryCSSLocalization (Space)
open OrdinarySegalHorizontalCotensor (cotensor)
open OrdinarySegalHorizontalCotensorPoint (constantSection)
open OrdinarySegalCotensorPointEvaluation (evaluation)

noncomputable section

private abbrev E (k : SimplexCategory) : SSet.{0} :=
  GroupoidSimplex.parameter.obj k

/-- The whole coherent homotopy on the original groupoid-simplex cotensor. -/
def homotopy (k : SimplexCategory) (j : Fin (k.len + 1)) (W : Space) :
    cotensor (E k) W ⟶ cotensor (E ⦋1⦌) (cotensor (E k) W) :=
  OrdinarySegalCotensorParameterHomotopy.homotopy
    (OrdinaryGroupoidSimplexCoherentContraction.contraction k j) W

/-- The original constant section followed by the specified evaluation is
strictly the identity, without any fibrancy assumption. -/
theorem section_evaluation (k : SimplexCategory) (j : Fin (k.len + 1)) (W : Space) :
    constantSection (E k) W ≫
        evaluation (E k) W (JTParameterContraction.parameterVertex k j) = 𝟙 W :=
  OrdinarySegalCotensorPointEvaluation.constantSection_evaluation _ _ _

/-- The time-zero endpoint of the whole homotopy is the actual identity. -/
theorem homotopy_zero (k : SimplexCategory) (j : Fin (k.len + 1)) (W : Space) :
    homotopy k j W ≫
        evaluation (E ⦋1⦌) (cotensor (E k) W)
          (JTParameterContraction.parameterVertex ⦋1⦌ 0) = 𝟙 (cotensor (E k) W) := by
  rw [homotopy, OrdinarySegalCotensorParameterHomotopy.homotopy_evaluation,
    ← Category.assoc,
    ← OrdinaryGroupoidSimplexCoherentContraction.slice_vertex,
    OrdinaryGroupoidSimplexCoherentContraction.contraction_zero,
    OrdinarySegalHorizontalCotensor.pre_id]

/-- The time-one endpoint is the original evaluation followed by the
original constant section at precisely the same selected vertex. -/
theorem homotopy_one (k : SimplexCategory) (j : Fin (k.len + 1)) (W : Space) :
    homotopy k j W ≫
        evaluation (E ⦋1⦌) (cotensor (E k) W)
          (JTParameterContraction.parameterVertex ⦋1⦌ 1) =
      evaluation (E k) W (JTParameterContraction.parameterVertex k j) ≫
        constantSection (E k) W := by
  rw [homotopy, OrdinarySegalCotensorParameterHomotopy.homotopy_evaluation,
    ← Category.assoc,
    ← OrdinaryGroupoidSimplexCoherentContraction.slice_vertex,
    OrdinaryGroupoidSimplexCoherentContraction.contraction_one,
    OrdinarySegalCotensorPointEvaluation.evaluation_constantSection,
    ← OrdinaryGroupoidSimplexCoherentContraction.constantAt_vertex]

#print axioms section_evaluation
#print axioms homotopy_zero
#print axioms homotopy_one

end
end DaggerModels.PartII.OrdinaryGroupoidSimplexCotensorHomotopyInverse
