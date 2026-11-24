import OriginalSmithModelRecovered
import DaggerModelsPartII.TheoremAStatement

/-!
# Combinatorial model structures from Smith data

The two small generating families in Smith combinatorial data generate the
two right lifting classes of the constructed model. This records the same
certificate of combinatoriality used in Theorem A for an arbitrary category.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra MorphismProperty

universe w v u

namespace DaggerModels.PartII.ModelProperties

/-- A model structure is combinatorial when its category is locally
presentable and both lifting systems have small generating families. -/
def combinatorial {C : Type u} [Category.{v} C] (M : ModelCategory C) : Prop :=
  letI := M
  IsLocallyPresentable.{w} C ∧
    ∃ I J : MorphismProperty C,
      IsSmall.{w} I ∧ IsSmall.{w} J ∧
        HasSmallObjectArgument.{w} I ∧ HasSmallObjectArgument.{w} J ∧
        I.rlp = trivialFibrations C ∧
        J.rlp = fibrations C

/-- Smith combinatorial data give the exact generating-family certificate
for the constructed model structure. -/
theorem combinatorial_of_smithData {C : Type u} [Category.{v} C]
    {I W : MorphismProperty C} (solution : DaggerSmithSolutionSet.SolutionData.{w} I W)
    (d : DaggerSmithSolutionSet.CombinatorialData solution) :
    combinatorial.{w} d.model := by
  letI := d.locallyPresentable
  letI : ModelCategory C := d.model
  letI : IsSmall.{w} I := d.smallI
  let J := DaggerSmithSolutionSet.J solution
  letI : IsSmall.{w} J := d.smallJ
  have hC : cofibrations C = I.rlp.llp := d.modelCof
  have hI : I.rlp = trivialFibrations C := by
    calc
      I.rlp = I.rlp.llp.rlp := (rlp_llp_rlp I).symm
      _ = (cofibrations C).rlp := congrArg MorphismProperty.rlp hC.symm
      _ = trivialFibrations C :=
        rlp_eq_of_wfs (cofibrations C) (trivialFibrations C)
  have hJ : J.rlp = fibrations C := d.fibrations.trans d.modelFib.symm
  exact ⟨d.locallyPresentable, I, J, d.smallI, d.smallJ,
    DaggerSmithSolutionSet.smallObjectArgument I,
    DaggerSmithSolutionSet.smallObjectArgument J, hI, hJ⟩

/-- For the resolution category, this generic certificate is definitionally
the combinatoriality clause in Theorem A. -/
theorem combinatorial_iff_theoremA (M : ModelCategory ResolutionDiagram.{u}) :
    combinatorial.{u} M ↔ TheoremAStatement.combinatorial M := Iff.rfl

end DaggerModels.PartII.ModelProperties
