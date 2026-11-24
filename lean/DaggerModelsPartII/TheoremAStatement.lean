import DaggerModelsPartII.ResolutionLocality

/-! Statement of Theorem A of Models for dagger categories II.
This specification imports the original coefficient model and the Part II
definitions of the diagram category, Reedy classes, and literal local tests. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

universe u

namespace DaggerModels.PartII.TheoremAStatement

noncomputable local instance theoremAChallengeLimits : HasLimits DaggerSSet.{u} :=
  daggerSSetHasLimits
noncomputable local instance theoremAChallengeColimits : HasColimits DaggerSSet.{u} :=
  daggerSSetHasColimits
noncomputable local instance theoremAChallengeCoefficient : ModelCategory DaggerSSet.{u} :=
  DaggerOriginalJoyalModel.standardModelCategory

/-- Left properness with respect to the supplied model structure. -/
def leftProper (M : ModelCategory ResolutionDiagram.{u}) : Prop :=
  letI := M
  ∀ {X Y X' Y' : ResolutionDiagram.{u}} {f : X ⟶ Y} {i : X ⟶ X'}
    {j : Y ⟶ Y'} {f' : X' ⟶ Y'}, IsPushout f i j f' →
    weakEquivalences ResolutionDiagram.{u} f → cofibrations ResolutionDiagram.{u} i →
    weakEquivalences ResolutionDiagram.{u} f'

/-- Small generating classes for the two lifting systems of the supplied model. -/
def combinatorial (M : ModelCategory ResolutionDiagram.{u}) : Prop :=
  letI := M
  IsLocallyPresentable.{u} ResolutionDiagram.{u} ∧
    ∃ I J : MorphismProperty ResolutionDiagram.{u},
      IsSmall.{u} I ∧ IsSmall.{u} J ∧
        HasSmallObjectArgument.{u} I ∧ HasSmallObjectArgument.{u} J ∧
        I.rlp = trivialFibrations ResolutionDiagram.{u} ∧
        J.rlp = fibrations ResolutionDiagram.{u}

/-- Theorem A, including the exact classes of the localization at the manuscript's
collapse maps and the constant–evaluation Quillen equivalence. -/
def statement : Prop :=
  ∃ M : ModelCategory ResolutionDiagram.{u},
    letI := M
    cofibrations ResolutionDiagram.{u} = reedyCofibrations ∧
      weakEquivalences ResolutionDiagram.{u} = resolutionLocalEquivalences ∧
      leftProper M ∧ combinatorial M ∧
      (∀ W : ResolutionDiagram.{u}, IsFibrant W ↔ resolutionLocalObject W) ∧
      (∀ W : ResolutionDiagram.{u}, IsFibrant W ↔
        @IsFibrant ResolutionDiagram.{u} _ resolutionReedyModelCategory.categoryWithFibrations _ W ∧
          reedyWeakEquivalences (resolutionCounit W)) ∧
      constantEvaluationAdjunction.{u}.IsQuillenEquivalence

end DaggerModels.PartII.TheoremAStatement
