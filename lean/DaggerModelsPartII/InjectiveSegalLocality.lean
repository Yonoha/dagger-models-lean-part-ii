import DaggerModelsPartII.ProjectiveInjectiveComparison
import DaggerModelsPartII.SegalSpaceConditions

/-!
# Strict and derived unitarily complete dagger Segal locality

The literal spine and walking-unitary tests characterize injective local
objects. Projective local objects are the levelwise Kan diagrams whose
injectively fibrant replacements satisfy these strict tests.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.SegalLocalizers

noncomputable section

local instance reversalInjectiveModel : ModelCategory ReverseDaggerSpace.{0} :=
  InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ

/-- The literal Segal and completeness tests characterize injective local objects. -/
theorem injectiveLocalObject_iff_strict (W : ReverseDaggerSpace.{0}) :
    Localization.localObject localizingFamily W ↔
      IsFibrant W ∧ unitarilyCompleteSegalCondition W := by
  constructor
  · rintro ⟨hW, h⟩
    letI := hW
    refine ⟨hW, (unitarilyCompleteSegalCondition_iff_family W).mpr ?_⟩
    intro A B f hf
    exact (InjectiveKanDiagram.model_homotopyMapping_iff_strict ReverseSimplexᵒᵖ f).mp
      (h f hf)
  · rintro ⟨hW, h⟩
    letI := hW
    refine ⟨hW, ?_⟩
    intro A B f hf
    exact (InjectiveKanDiagram.model_homotopyMapping_iff_strict ReverseSimplexᵒᵖ f).mpr
      ((unitarilyCompleteSegalCondition_iff_family W).mp h f hf)

/-- The manuscript's derived condition includes levelwise Kan fibrancy and a
levelwise weak equivalence to an injectively fibrant strict Segal-complete object. -/
def derivedUnitarilyCompleteSegalCondition (W : ReverseDaggerSpace.{0}) : Prop :=
  (∀ d, IsFibrant (W.obj d)) ∧
    ∃ (W' : ReverseDaggerSpace.{0}) (r : W ⟶ W'),
      (HomotopicalAlgebra.weakEquivalences SSet.{0}).functorCategory ReverseSimplexᵒᵖ r ∧
        IsFibrant W' ∧ unitarilyCompleteSegalCondition W'

/-- Projective local objects are precisely the levelwise Kan diagrams that
are unitarily complete dagger Segal spaces in the derived sense. -/
theorem projectiveLocalObject_iff_derived (W : ReverseDaggerSpace.{0}) :
    (letI := ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ;
      Localization.localObject localizingFamily W) ↔
        derivedUnitarilyCompleteSegalCondition W := by
  constructor
  · intro h
    obtain ⟨W', r, hr, hl⟩ :=
      (ProjectiveInjectiveComparison.localObject_iff_exists_injectiveLocal
        ReverseSimplexᵒᵖ localizingFamily W h.1).mp h
    exact ⟨(ProjectiveKanDiagram.model_isFibrant_iff ReverseSimplexᵒᵖ W).mp h.1,
      W', r, hr, (injectiveLocalObject_iff_strict W').mp hl⟩
  · rintro ⟨hW, W', r, hr, hl⟩
    have hWp := (ProjectiveKanDiagram.model_isFibrant_iff ReverseSimplexᵒᵖ W).mpr hW
    exact (ProjectiveInjectiveComparison.localObject_iff_exists_injectiveLocal
      ReverseSimplexᵒᵖ localizingFamily W hWp).mpr
        ⟨W', r, hr, (injectiveLocalObject_iff_strict W').mpr hl⟩

/-- Every injectively fibrant replacement along a levelwise weak equivalence
computes the derived Segal-completeness condition of a projectively fibrant source. -/
theorem projectiveLocalObject_iff_strict_replacement
    {W W' : ReverseDaggerSpace.{0}}
    (hW : letI := ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    [IsFibrant W'] (r : W ⟶ W')
    (hr : (HomotopicalAlgebra.weakEquivalences SSet.{0}).functorCategory
      ReverseSimplexᵒᵖ r) :
    (letI := ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ;
      Localization.localObject localizingFamily W) ↔
        unitarilyCompleteSegalCondition W' := by
  have hW'i : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ;
      IsFibrant W' := inferInstance
  have htarget :
      (letI := ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ;
        Localization.localObject localizingFamily W) ↔
      (letI := ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ;
        Localization.localObject localizingFamily W') := by
    letI := ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
    letI := hW
    letI := ProjectiveInjectiveComparison.isFibrant_projective ReverseSimplexᵒᵖ W'
      hW'i
    exact Localization.localObject_iff_of_weak localizingFamily r hr
  have hmodels := ProjectiveInjectiveComparison.localObject_iff_on_injectiveFibrant
    ReverseSimplexᵒᵖ localizingFamily W' hW'i
  exact htarget.trans (hmodels.trans ((injectiveLocalObject_iff_strict W').trans
    ⟨fun h ↦ h.2, fun h ↦ ⟨inferInstance, h⟩⟩))

end

end DaggerModels.PartII.SegalLocalizers
