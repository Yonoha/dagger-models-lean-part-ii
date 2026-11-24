import DaggerModelsPartII.ResolutionLocalizationProper
import DaggerModelsPartII.SourceResolutionTowerConstruction

/-! Smith recognition for the precise Part II localization classes. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

universe u

namespace DaggerModels.PartII

noncomputable section

local instance localizationSmithLimits : HasLimits DaggerSSet.{u} := daggerSSetHasLimits
local instance localizationSmithColimits : HasColimits DaggerSSet.{u} := daggerSSetHasColimits
local instance localizationSmithCoefficientModel : ModelCategory DaggerSSet.{u} :=
  DaggerOriginalJoyalModel.standardModelCategory

section Reedy

local instance localizationSmithReedyModel : ModelCategory ResolutionDiagram.{u} :=
  resolutionReedyModelCategory

theorem resolutionReedyI_rlp_llp :
    resolutionReedyI.{u}.rlp.llp = reedyCofibrations := by
  rw [resolutionReedyI_rlp]
  exact llp_eq_of_wfs (cofibrations ResolutionDiagram.{u}) (trivialFibrations ResolutionDiagram.{u})

theorem resolutionReedyI_rlp_le_localEquivalences :
    resolutionReedyI.{u}.rlp ≤ resolutionLocalEquivalences := by
  rw [resolutionReedyI_rlp]
  exact fun _ _ f hf ↦ reedyWeakEquivalences_le_resolutionLocalEquivalences f hf.2

end Reedy

/-- Smith recognition with the literal Reedy generators and the literal (S_h)-local
weak class. Cobase-change stability is supplied by the local pushout theorem. -/
def resolutionLocalizationSmithData
    (S : DaggerSmithSolutionSet.SolutionData.{u} resolutionReedyI.{u} resolutionLocalEquivalences) :
    DaggerSmithSolutionSet.CombinatorialData S := by
  letI := resolutionDiagramLocallyPresentable.{u}
  letI : (resolutionReedyI.{u}.rlp.llp ⊓ resolutionLocalEquivalences).IsStableUnderCobaseChange := by
    rw [resolutionReedyI_rlp_llp]
    infer_instance
  letI : IsStableUnderTransfiniteComposition.{u}
      (resolutionReedyI.{u}.rlp.llp ⊓ resolutionLocalEquivalences) := by
    rw [resolutionReedyI_rlp_llp]
    infer_instance
  exact DaggerSmithSolutionSet.combinatorialData S resolutionReedyI_rlp_le_localEquivalences

/-- The exact classes provided by the Smith construction, assuming its closure and
solution-set hypotheses. -/
theorem resolutionLocalizationSmith_exactClasses
    (S : DaggerSmithSolutionSet.SolutionData.{u} resolutionReedyI.{u} resolutionLocalEquivalences) :
    (resolutionLocalizationSmithData S).model.categoryWithCofibrations.cofibrations =
      reedyCofibrations ∧
    (resolutionLocalizationSmithData S).model.categoryWithWeakEquivalences.weakEquivalences =
      resolutionLocalEquivalences :=
  ⟨(resolutionLocalizationSmithData S).modelCof.trans resolutionReedyI_rlp_llp,
    (resolutionLocalizationSmithData S).modelWeak⟩

end

end DaggerModels.PartII
