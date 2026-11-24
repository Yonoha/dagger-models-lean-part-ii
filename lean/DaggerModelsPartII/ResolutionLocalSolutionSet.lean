import DaggerModelsPartII.LocalFibrantReplacement
import DaggerModelsPartII.ResolutionLocalizationSmith
import OriginalAccessibleInverseImageRecovered
import OriginalAccessibleSolutionsRecovered

/-! A small Smith solution set for the literal Part II local weak equivalences. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite Simplicial

universe u

namespace DaggerModels.PartII

noncomputable section

local instance localSolutionLimits : HasLimits DaggerSSet.{u} := daggerSSetHasLimits
local instance localSolutionColimits : HasColimits DaggerSSet.{u} := daggerSSetHasColimits
local instance localSolutionCoefficientModel : ModelCategory DaggerSSet.{u} :=
  DaggerOriginalJoyalModel.standardModelCategory
local instance localSolutionReedyModel : ModelCategory ResolutionDiagram.{u} :=
  resolutionReedyModelCategory

private def localDetectionFunctor : ResolutionDiagram.{u} ⥤ DaggerSSet.{u} :=
  resolutionLocalFibrantReplacement ⋙ evaluationAt 0

private theorem localDetectionArrow_accessible :
    Functor.IsAccessible.{u} localDetectionFunctor.{u}.mapArrow := by
  obtain ⟨κ, hκ, hR⟩ := resolutionLocalFibrantReplacement_accessible.{u}.exists_cardinal
  letI := hκ
  letI := hR
  letI : (evaluationAt.{u} 0).IsCardinalAccessible κ := by
    constructor
    intro J _ _
    change PreservesColimitsOfShape J ((evaluation SimplexCategoryᵒᵖ DaggerSSet.{u}).obj (op ⦋0⦌))
    infer_instance
  letI : localDetectionFunctor.{u}.IsCardinalAccessible κ := by
    unfold localDetectionFunctor
    infer_instance
  letI := mapArrow_isCardinalAccessible localDetectionFunctor κ
  exact Functor.isAccessible_of_isCardinalAccessible _ κ

private theorem coefficientWeakArrow_eq :
    DaggerAccessibleSolutions.arrowProperty (weakEquivalences DaggerSSet.{u}) =
      DaggerActualWeakAccessibility.WDArrow DaggerUnitaryInvariance.standardReplacement.{u} := by
  change DaggerAccessibleSolutions.arrowProperty
    DaggerOriginalJoyalModel.standardModelCategory.categoryWithWeakEquivalences.weakEquivalences = _
  rw [DaggerOriginalJoyalModel.standard_model_weak]

/-- The exact local weak class has a small solution set for the actual Reedy generators. -/
def resolutionLocalSolutionSet :
    DaggerSmithSolutionSet.SolutionData.{u} resolutionReedyI.{u} resolutionLocalEquivalences := by
  letI := resolutionDiagramLocallyPresentable.{u}
  letI := daggerSSetLocallyPresentable.{u}
  letI := DaggerRLPAccessibility.arrowLocallyPresentable (ResolutionDiagram.{u})
  letI := DaggerRLPAccessibility.arrowLocallyPresentable (DaggerSSet.{u})
  let F := localDetectionFunctor.{u}.mapArrow
  let W := DaggerAccessibleSolutions.arrowProperty (weakEquivalences DaggerSSet.{u})
  letI : W.IsClosedUnderIsomorphisms := by
    constructor
    intro A B e h
    exact ((weakEquivalences DaggerSSet.{u}).arrow_iso_iff e).mp h
  letI : Functor.IsAccessible.{u} F := localDetectionArrow_accessible
  let E := DaggerActualWeakAccessibility.standard_wd_accessibility.{u}
  let κ := E.choose
  let hκ := E.choose_spec.choose
  letI := hκ
  have hdata := E.choose_spec.choose_spec.choose_spec
  letI : IsCardinalAccessibleCategory W.FullSubcategory κ := by
    simpa only [W, coefficientWeakArrow_eq] using hdata.2.2.1
  letI : W.ι.IsCardinalAccessible κ := by
    simpa only [W, coefficientWeakArrow_eq] using hdata.2.2.2
  letI : IsAccessibleCategory.{u} W.FullSubcategory := ⟨⟨κ, hκ, inferInstance⟩⟩
  letI : Functor.IsAccessible.{u} W.ι := Functor.isAccessible_of_isCardinalAccessible _ κ
  have he : DaggerAccessibleSolutions.arrowProperty resolutionLocalEquivalences.{u} =
      W.inverseImage F := by
    rw [resolutionLocalEquivalences_eq_inverseImage]
    rfl
  letI : IsAccessibleCategory.{u}
      (DaggerAccessibleSolutions.arrowProperty resolutionLocalEquivalences.{u}).FullSubcategory :=
    he.symm ▸ DaggerAccessibleInverseImage.inverseImage_isAccessible F W
  letI : Functor.IsAccessible.{u}
      (DaggerAccessibleSolutions.arrowProperty resolutionLocalEquivalences.{u}).ι :=
    he.symm ▸ DaggerAccessibleInverseImage.inverseImage_inclusion_isAccessible F W
  exact DaggerAccessibleSolutions.ofAccessible resolutionReedyI resolutionLocalEquivalences

end

end DaggerModels.PartII
