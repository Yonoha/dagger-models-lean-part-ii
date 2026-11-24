import OrdinaryJTNativeMapReedy
import OrdinaryJTMappingPostWeak
import DaggerModelsPartII.ProjectiveKanDiagram

/-!
# The actual ordinary JT adjunction before Segal localization

The curried original right adjoint preserves native Kan Reedy fibrations
by `OrdinaryJTNativeMapReedy`, hence levelwise fibrations by the existing
`reedyMatchingFibration_eval`. The checked target mapping-frame theorem
preserves trivial fibrations at every literal row. The existing Quillen
adjunction criterion therefore applies to the projective Kan diagram model
and the original Joyal model. This is not the localized CSS equivalence.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryJTProjectiveQuillen

open OrdinaryJTCurriedAdjunction OrdinaryJTNativeMapReedy
open OrdinaryJTNativeRightNerveReedy OrdinaryJTPlainMapReedy

noncomputable section

/-- The original ordinary Joyal model, not the native Kan coefficient model. -/
def joyalModel : ModelCategory SSet.{0} :=
  DaggerActualDCHRightInducedAndMainTheoremD.ordinaryJoyalModel.{0}

/-- The projective Kan model on the actual curried input category. -/
def diagramModel : ModelCategory (SimplexCategoryᵒᵖ ⥤ SSet.{0}) :=
  ProjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- The actual right adjoint preserves fibrations into the projective Kan model. -/
theorem right_map_fibration {X Y : SSet.{0}} (p : X ⟶ Y)
    (hp : joyalModel.categoryWithFibrations.fibrations p) :
    diagramModel.categoryWithFibrations.fibrations (right.map p) := by
  have h := right_map_relativeReedyFibration p hp
  change ProjectiveKanDiagram.fibrations SimplexCategoryᵒᵖ (right.map p)
  intro m
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, op ⦋n⦌ = m :=
    ⟨m.unop.len, congrArg op (SimplexCategory.ext _ _ rfl)⟩
  exact reedyMatchingFibration_eval (right.map p) h n

/-- Each actual right-nerve row map is the corresponding plain mapping map. -/
def rowArrowIso {X Y : SSet.{0}} (p : X ⟶ Y)
    (m : SimplexCategoryᵒᵖ) :
    Arrow.mk ((right.map p).app m) ≅
      Arrow.mk ((plainMap p).app m) :=
  Arrow.isoMk ((nativePlainIso X).app m) ((nativePlainIso Y).app m)
    (congr_app (nativePlainIso_naturality p) m).symm

/-- Original Joyal trivial fibrations induce levelwise native Kan trivial fibrations. -/
theorem right_map_trivialFibration {X Y : SSet.{0}} (p : X ⟶ Y)
    (hp : joyalModel.categoryWithFibrations.fibrations p)
    (hw : joyalModel.categoryWithWeakEquivalences.weakEquivalences p) :
    diagramModel.categoryWithFibrations.fibrations (right.map p) ∧
      diagramModel.categoryWithWeakEquivalences.weakEquivalences (right.map p) := by
  have hweak : DaggerNativeJoyalMappingTest.weakCategoricalEquivalences p := by
    have he := DaggerNativeOriginalJoyalSmithModelData.modelData.modelWeak
    change joyalModel.categoryWithWeakEquivalences.weakEquivalences =
      DaggerNativeJoyalMappingTest.weakCategoricalEquivalences at he
    exact he ▸ hw
  have hrows (m : SimplexCategoryᵒᵖ) :
      trivialFibrations SSet.{0} ((right.map p).app m) := by
    have h := OrdinaryJTMappingPostWeak.mappingPost_trivialFibration p hp hweak
      (SSet.stdSimplex.obj m.unop)
    exact ((trivialFibrations SSet.{0}).arrow_mk_iso_iff (rowArrowIso p m)).mpr h
  exact ⟨fun m ↦ (hrows m).1, fun m ↦ (hrows m).2⟩

/-- The original curried realization--nerve adjunction is Quillen from the
projective Kan diagram model to the original Joyal model before localization. -/
theorem isQuillenAdjunction :
    @Adjunction.IsQuillenAdjunction (SimplexCategoryᵒᵖ ⥤ SSet.{0}) SSet.{0}
      _ _ diagramModel joyalModel left right adjunction := by
  letI : ModelCategory (SimplexCategoryᵒᵖ ⥤ SSet.{0}) := diagramModel
  letI : ModelCategory SSet.{0} := joyalModel
  letI : CategoryWithFibrations SSet.{0} := joyalModel.categoryWithFibrations
  letI : CategoryWithCofibrations SSet.{0} := joyalModel.categoryWithCofibrations
  letI : CategoryWithWeakEquivalences SSet.{0} :=
    joyalModel.categoryWithWeakEquivalences
  letI : right.PreservesFibrations := right.preservesFibrations_iff.mpr
    (fun _ _ p hp ↦ right_map_fibration p hp)
  have htriv : right.PreservesTrivialFibrations :=
    ⟨fun _ _ p hp ↦ right_map_trivialFibration p hp.1 hp.2⟩
  letI : left.PreservesCofibrations :=
    adjunction.preservesTrivialFibrations_iff_preservesCofibrations.mp htriv
  exact ⟨⟩

#print axioms right_map_fibration
#print axioms right_map_trivialFibration
#print axioms isQuillenAdjunction

end

end DaggerModels.PartII.OrdinaryJTProjectiveQuillen
