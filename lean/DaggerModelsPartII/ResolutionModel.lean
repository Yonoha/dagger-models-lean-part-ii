import DaggerModelsPartII.ResolutionLocalSolutionSet

/-! Theorem A: the resolution model structure of Models for dagger categories II. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

universe u

namespace DaggerModels.PartII

noncomputable section

local instance resolutionModelLimits : HasLimits DaggerSSet.{u} := daggerSSetHasLimits
local instance resolutionModelColimits : HasColimits DaggerSSet.{u} := daggerSSetHasColimits
local instance resolutionModelCoefficientModel : ModelCategory DaggerSSet.{u} :=
  DaggerOriginalJoyalModel.standardModelCategory

/-- The combinatorial data for the actual (S_h)-localization of the Reedy model. -/
def resolutionLocalizedCombinatorialData :
    DaggerSmithSolutionSet.CombinatorialData resolutionLocalSolutionSet.{u} :=
  resolutionLocalizationSmithData resolutionLocalSolutionSet

/-- Part II, `cs.def.Sh`. The resolution model structure on simplicial dagger simplicial sets. -/
def resolutionLocalizedModelCategory : ModelCategory ResolutionDiagram.{u} :=
  resolutionLocalizedCombinatorialData.model

local instance resolutionLocalizedModelInstance : ModelCategory ResolutionDiagram.{u} :=
  resolutionLocalizedModelCategory

theorem resolutionLocalized_cofibrations :
    cofibrations ResolutionDiagram.{u} = reedyCofibrations :=
  (resolutionLocalizationSmith_exactClasses resolutionLocalSolutionSet).1

theorem resolutionLocalized_weakEquivalences :
    weakEquivalences ResolutionDiagram.{u} = resolutionLocalEquivalences :=
  (resolutionLocalizationSmith_exactClasses resolutionLocalSolutionSet).2

theorem resolutionLocalized_leftProper
    {X Y X' Y' : ResolutionDiagram.{u}} {f : X ⟶ Y} {i : X ⟶ X'}
    {j : Y ⟶ Y'} {f' : X' ⟶ Y'} (sq : IsPushout f i j f')
    (hf : weakEquivalences ResolutionDiagram.{u} f) (hi : cofibrations ResolutionDiagram.{u} i) :
    weakEquivalences ResolutionDiagram.{u} f' :=
  resolutionLocalizedModel_leftProper resolutionLocalized_cofibrations
    resolutionLocalized_weakEquivalences sq hf hi

/-- Part II, `cs.def.Sh`. The localization is combinatorial. -/
theorem resolutionLocalized_combinatorial :
    IsLocallyPresentable.{u} ResolutionDiagram.{u} ∧
      ∃ I J : MorphismProperty ResolutionDiagram.{u},
        IsSmall.{u} I ∧ IsSmall.{u} J ∧
          HasSmallObjectArgument.{u} I ∧ HasSmallObjectArgument.{u} J ∧
          I.rlp = trivialFibrations ResolutionDiagram.{u} ∧
          J.rlp = fibrations ResolutionDiagram.{u} := by
  letI := resolutionDiagramLocallyPresentable.{u}
  let D := resolutionLocalizedCombinatorialData.{u}
  let J := DaggerSmithSolutionSet.J resolutionLocalSolutionSet.{u}
  letI : IsSmall.{u} J := D.smallJ
  have hJ : J.rlp = fibrations ResolutionDiagram.{u} := D.fibrations.trans D.modelFib.symm
  have hI : resolutionReedyI.{u}.rlp = trivialFibrations ResolutionDiagram.{u} := by
    change resolutionReedyI.{u}.rlp =
      fibrations ResolutionDiagram.{u} ⊓ weakEquivalences ResolutionDiagram.{u}
    rw [← hJ, resolutionLocalized_weakEquivalences]
    exact D.trivialFibrations.symm
  exact ⟨resolutionDiagramLocallyPresentable, resolutionReedyI, J, D.smallI, D.smallJ,
    resolutionSmallObjectArgument _, resolutionSmallObjectArgument _, hI, hJ⟩

theorem resolutionLocalized_isFibrant_iff_local (W : ResolutionDiagram.{u}) :
    IsFibrant W ↔ resolutionLocalObject W :=
  localizedModel_isFibrant_iff_resolutionLocalObject resolutionLocalized_cofibrations
    resolutionLocalized_weakEquivalences W

/-- Part II, `cs.thm.resolution`. Localized fibrancy is Reedy fibrancy and
levelwise weak equivalence of the constant-diagram counit. -/
theorem resolutionLocalized_isFibrant_iff (W : ResolutionDiagram.{u}) :
    IsFibrant W ↔
      @IsFibrant ResolutionDiagram.{u} _ resolutionReedyModelCategory.categoryWithFibrations _ W ∧
        reedyWeakEquivalences (resolutionCounit W) :=
  localizedModel_isFibrant_iff_homotopicallyConstant resolutionLocalized_cofibrations
    resolutionLocalized_weakEquivalences W

/-- Part II, `cs.thm.equivalence`. Constant diagrams and zero evaluation
form a Quillen equivalence with the original dagger Joyal model. -/
theorem resolutionLocalized_constantEvaluation :
    constantEvaluationAdjunction.{u}.IsQuillenEquivalence :=
  constantEvaluation_isQuillenEquivalence_of_exactClasses resolutionLocalized_cofibrations
    resolutionLocalized_weakEquivalences

end

end DaggerModels.PartII
