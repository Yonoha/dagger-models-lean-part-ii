import DaggerModelsPartII.MappingCofibrationInclusion
import DaggerModelsPartII.InjectiveKanModel
import DaggerModelsPartII.LocalEquivalenceClasses

/-!
# Projective and injective derived mapping tests

The two Kan diagram models have the same weak equivalences. Projective
cofibrations are injective cofibrations, so an injectively fibrant target
can be tested with source frames from either model.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.ProjectiveInjectiveComparison

noncomputable section

variable (C : Type u) [Category.{u} C]

/-- Every projective cofibration is an injective cofibration. -/
theorem cofibrations_le :
    (ProjectiveKanDiagram.modelCategory C).categoryWithCofibrations.cofibrations ≤
      (InjectiveKanDiagram.modelCategory C).categoryWithCofibrations.cofibrations := by
  intro A B f hf
  have hm : Mono f := (NatTrans.mono_iff_mono_app f).mpr
    (ProjectiveKanDiagram.boundaryCofibrations_levelwiseMono C f hf)
  have heq := InjectiveKanDiagram.model_cofibrations C
  change (InjectiveKanDiagram.modelCategory C).categoryWithCofibrations.cofibrations =
    monomorphisms _ at heq
  change (InjectiveKanDiagram.modelCategory C).categoryWithCofibrations.cofibrations f
  rw [heq]
  exact hm

/-- The projective and injective models have identical weak-equivalence classes. -/
theorem weakEquivalences_eq :
    (ProjectiveKanDiagram.modelCategory C).categoryWithWeakEquivalences.weakEquivalences =
      (InjectiveKanDiagram.modelCategory C).categoryWithWeakEquivalences.weakEquivalences :=
  (ProjectiveKanDiagram.model_weakEquivalences C).trans
    (InjectiveKanDiagram.model_weakEquivalences C).symm

/-- Every injective fibration is a projective fibration. -/
theorem fibrations_le :
    (InjectiveKanDiagram.modelCategory C).categoryWithFibrations.fibrations ≤
      (ProjectiveKanDiagram.modelCategory C).categoryWithFibrations.fibrations :=
  fibrations_le_of_cofibrations_le _ _ (cofibrations_le C) (weakEquivalences_eq C)

/-- An injectively fibrant diagram is also projectively fibrant. -/
theorem isFibrant_projective (W : C ⥤ SSet.{u})
    (hW : letI := InjectiveKanDiagram.modelCategory C; IsFibrant W) :
    letI := ProjectiveKanDiagram.modelCategory C; IsFibrant W := by
  have hp : (InjectiveKanDiagram.modelCategory C).categoryWithFibrations.fibrations
      (terminal.from W) := by
    letI := InjectiveKanDiagram.modelCategory C
    letI := hW
    exact mem_fibrations _
  letI := ProjectiveKanDiagram.modelCategory C
  exact (fibration_iff _).mpr (fibrations_le C _ hp)

/-- Into an injectively fibrant target, both models give the same derived test. -/
theorem homotopyMapping_iff (W : C ⥤ SSet.{u})
    (hW : letI := InjectiveKanDiagram.modelCategory C; IsFibrant W)
    {A B : C ⥤ SSet.{u}} (f : A ⟶ B) :
    (letI := ProjectiveKanDiagram.modelCategory C; homotopyMappingWeakEquivalences W f) ↔
      (letI := InjectiveKanDiagram.modelCategory C; homotopyMappingWeakEquivalences W f) :=
  homotopyMappingWeakEquivalences_iff_of_cofibrations_le _ _
    (cofibrations_le C) (weakEquivalences_eq C) W (isFibrant_projective C W hW) hW f

/-- On an injectively fibrant target, both models have the same locality test. -/
theorem localObject_iff_on_injectiveFibrant (S : MorphismProperty (C ⥤ SSet.{u}))
    (W : C ⥤ SSet.{u})
    (hW : letI := InjectiveKanDiagram.modelCategory C; IsFibrant W) :
    (letI := ProjectiveKanDiagram.modelCategory C; Localization.localObject S W) ↔
      (letI := InjectiveKanDiagram.modelCategory C; Localization.localObject S W) := by
  constructor
  · rintro ⟨_, h⟩
    exact ⟨hW, fun A B f hf ↦ (homotopyMapping_iff C W hW f).mp (h f hf)⟩
  · rintro ⟨_, h⟩
    exact ⟨isFibrant_projective C W hW,
      fun A B f hf ↦ (homotopyMapping_iff C W hW f).mpr (h f hf)⟩

/-- Every diagram has an injectively fibrant replacement along a levelwise weak equivalence. -/
theorem exists_injectiveFibrantReplacement (W : C ⥤ SSet.{u}) :
    ∃ (W' : C ⥤ SSet.{u}) (r : W ⟶ W'),
      (ProjectiveKanDiagram.modelCategory C).categoryWithWeakEquivalences.weakEquivalences r ∧
        (letI := InjectiveKanDiagram.modelCategory C; IsFibrant W') := by
  letI := InjectiveKanDiagram.modelCategory C
  let d := factorizationData (HomotopicalAlgebra.trivialCofibrations (C ⥤ SSet.{u}))
    (HomotopicalAlgebra.fibrations (C ⥤ SSet.{u})) (terminal.from W)
  refine ⟨d.Z, d.i, ?_, ?_⟩
  · rw [weakEquivalences_eq C]
    exact d.hi.2
  · exact (isFibrant_iff_of_isTerminal d.p terminalIsTerminal).mpr
      ((fibration_iff _).mpr d.hp)

/-- Projective locality of a projectively fibrant diagram is injective locality
of an injectively fibrant replacement along a levelwise weak equivalence. -/
theorem localObject_iff_exists_injectiveLocal (S : MorphismProperty (C ⥤ SSet.{u}))
    (W : C ⥤ SSet.{u})
    (hW : letI := ProjectiveKanDiagram.modelCategory C; IsFibrant W) :
    (letI := ProjectiveKanDiagram.modelCategory C; Localization.localObject S W) ↔
      ∃ (W' : C ⥤ SSet.{u}) (r : W ⟶ W'),
        (ProjectiveKanDiagram.modelCategory C).categoryWithWeakEquivalences.weakEquivalences r ∧
          (letI := InjectiveKanDiagram.modelCategory C; Localization.localObject S W') := by
  constructor
  · intro h
    obtain ⟨W', r, hr, hW'⟩ := exists_injectiveFibrantReplacement C W
    have hl : letI := ProjectiveKanDiagram.modelCategory C;
        Localization.localObject S W' := by
      letI := ProjectiveKanDiagram.modelCategory C
      letI := hW
      letI := isFibrant_projective C W' hW'
      exact (Localization.localObject_iff_of_weak S r hr).mp h
    exact ⟨W', r, hr, (localObject_iff_on_injectiveFibrant C S W' hW').mp hl⟩
  · rintro ⟨W', r, hr, hl⟩
    have hl' := (localObject_iff_on_injectiveFibrant C S W' hl.1).mpr hl
    letI := ProjectiveKanDiagram.modelCategory C
    letI := hW
    letI := hl'.1
    exact (Localization.localObject_iff_of_weak S r hr).mpr hl'

/-- Projective and injective localization at the same family define the same weak class. -/
theorem localEquivalences_eq (S : MorphismProperty (C ⥤ SSet.{u})) :
    (letI := ProjectiveKanDiagram.modelCategory C; Localization.localEquivalences S) =
      (letI := InjectiveKanDiagram.modelCategory C; Localization.localEquivalences S) := by
  ext A B f
  constructor
  · intro hf Z hZ
    have hZp := (localObject_iff_on_injectiveFibrant C S Z hZ.1).mpr hZ
    exact (homotopyMapping_iff C Z hZ.1 f).mp (hf Z hZp)
  · intro hf Z hZ
    obtain ⟨Z', r, hr, hZ'⟩ :=
      (localObject_iff_exists_injectiveLocal C S Z hZ.1).mp hZ
    have hm := (homotopyMapping_iff C Z' hZ'.1 f).mpr (hf Z' hZ')
    letI := ProjectiveKanDiagram.modelCategory C
    letI := hZ.1
    letI := isFibrant_projective C Z' hZ'.1
    exact (homotopyMappingWeakEquivalences_target_iff r hr f).mpr hm

/-- The identity adjunction is a Quillen equivalence between the underlying models. -/
theorem identity_isQuillenEquivalence :
    @Adjunction.IsQuillenEquivalence (C ⥤ SSet.{u}) (C ⥤ SSet.{u}) _ _
      (ProjectiveKanDiagram.modelCategory C) (InjectiveKanDiagram.modelCategory C)
      (𝟭 _) (𝟭 _) Adjunction.id :=
  identity_isQuillenEquivalence_of_cofibrations_le _ _
    (cofibrations_le C) (weakEquivalences_eq C)

end

end DaggerModels.PartII.ProjectiveInjectiveComparison
