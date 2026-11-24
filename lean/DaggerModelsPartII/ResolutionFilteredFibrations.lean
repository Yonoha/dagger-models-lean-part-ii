import DaggerModelsPartII.ReedyCombinatorial
import DaggerModelsPartII.FilteredLifting

/-! Filtered colimits of Reedy trivial fibrations in the Part II diagram category. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite Simplicial

universe u t z

namespace DaggerModels.PartII

noncomputable section

attribute [local instance] Cardinal.fact_isRegular_aleph0

local instance filteredFibrationsLimits : HasLimits DaggerSSet.{u} := daggerSSetHasLimits
local instance filteredFibrationsColimits : HasColimits DaggerSSet.{u} := daggerSSetHasColimits
local instance filteredFibrationsCoefficientModel : ModelCategory DaggerSSet.{u} := DaggerOriginalJoyalModel.standardModelCategory
local instance filteredFibrationsReedyModel : ModelCategory ResolutionDiagram.{u} := resolutionReedyModelCategory

/-- The actual Reedy generating cofibrations have finitely presentable endpoints. -/
theorem resolutionReedyI_finitelyPresentable {A B : ResolutionDiagram.{u}}
    (f : A ⟶ B) (hf : resolutionReedyI f) :
    IsFinitelyPresentable.{u} A ∧ IsFinitelyPresentable.{u} B := by
  have he : DaggerActualWeakAccessibility.originalID.{u} =
      DaggerModels.freeBoundaryGenerators DaggerModels.freeDagger.{u} :=
    DaggerActualWeakAccessibility.originalID_eq
  change reedyBoundaryGenerators DaggerActualWeakAccessibility.originalID f at hf
  rw [he] at hf
  obtain ⟨⟨n, ⟨⟨X, Y, i⟩, hi⟩⟩⟩ := hf
  obtain ⟨m⟩ := hi
  letI := freeDagger_obj_isFinitelyPresentable (SSet.boundary.{u} m).toSSet
  letI := freeDagger_obj_isFinitelyPresentable (Δ[m] : SSet.{u})
  exact reedyBoundaryBox_finitelyPresentable n (DaggerModels.freeDagger.map (SSet.boundary m).ι)

/-- Reedy trivial fibrations are preserved under filtered colimits of arrows.
The colimit is specified on the source and target separately. -/
theorem resolutionReedy_trivialFibration_of_filteredColimit
    {J : Type t} [Category.{z} J] [EssentiallySmall.{u} J] [IsFiltered J]
    {F G : J ⥤ ResolutionDiagram.{u}} (p : F ⟶ G)
    {cF : Cocone F} {cG : Cocone G} (hF : IsColimit cF) (hG : IsColimit cG)
    (q : cF.pt ⟶ cG.pt) (hq : ∀ j, cF.ι.app j ≫ q = p.app j ≫ cG.ι.app j)
    (hp : ∀ j, trivialFibrations ResolutionDiagram.{u} (p.app j)) :
    trivialFibrations ResolutionDiagram.{u} q := by
  letI : IsCardinalFiltered J Cardinal.aleph0.{u} :=
    (isCardinalFiltered_aleph0_iff J).mpr inferInstance
  rw [← resolutionReedyI_rlp] at hp ⊢
  exact rlp_of_filteredColimit (κ := Cardinal.aleph0.{u}) p hF hG q hq
    resolutionReedyI (fun i hi ↦ resolutionReedyI_finitelyPresentable i hi) hp

end

end DaggerModels.PartII
