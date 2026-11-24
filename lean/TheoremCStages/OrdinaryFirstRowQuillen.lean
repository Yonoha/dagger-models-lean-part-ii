import OrdinaryFirstRowAdjunction
import OrdinaryCSSHorizontalWeak
import TopCatModelCategory.QuillenAdjunction

/-!
# The actual ordinary first-row Quillen adjunction

Ordinary horizontal discretization preserves literal monomorphisms and
sends each original Joyal weak map to a rowwise Joyal weak map. The checked
horizontal-to-CSS comparison therefore proves the actual first-row pair is
Quillen for the original Joyal model and the fixed CSS localization.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory HomotopicalAlgebra

namespace DaggerModels.PartII.OrdinaryFirstRowQuillen

open OrdinaryCSSLocalization (Space discrete)
open OrdinaryFirstRowAdjunction (firstRow adjunction)
open OrdinaryJTProjectiveQuillen (joyalModel)

noncomputable section

private local instance : ModelCategory SSet.{0} := joyalModel
private local instance : CategoryWithFibrations SSet.{0} := joyalModel.categoryWithFibrations
private local instance : CategoryWithCofibrations SSet.{0} := joyalModel.categoryWithCofibrations
private local instance : CategoryWithWeakEquivalences SSet.{0} :=
  joyalModel.categoryWithWeakEquivalences
private local instance : ModelCategory Space := OrdinaryCSSLocalization.model

/-- Every original Joyal cofibration remains a cofibration after the exact
ordinary horizontal discretization into the CSS model. -/
theorem discrete_map_cofibration {X Y : SSet.{0}} (f : X ⟶ Y)
    (hf : cofibrations SSet.{0} f) : cofibrations Space (discrete.map f) := by
  have hm : Mono f := by
    change joyalModel.categoryWithCofibrations.cofibrations f at hf
    rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelCof,
      DaggerNativeFullWeakSmithGenerators.boundary_cof] at hf
    exact hf
  haveI := hm
  change OrdinaryCSSLocalization.model.categoryWithCofibrations.cofibrations
    (discrete.map f)
  rw [OrdinaryCSSLocalization.exactClasses.1]
  letI : ModelCategory Space := InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ
  change cofibrations Space (discrete.map f)
  rw [InjectiveKanDiagram.model_cofibrations]
  exact OrdinaryCSSLocalization.discrete_map_mono f

/-- Original Joyal weak maps become actual CSS weak maps under horizontal
discretization, without a fibrancy assumption on either simplicial set. -/
theorem discrete_map_weak {X Y : SSet.{0}} (f : X ⟶ Y)
    (hf : weakEquivalences SSet.{0} f) : weakEquivalences Space (discrete.map f) := by
  apply OrdinaryCSSHorizontalWeak.weak_of_rows
  intro k
  change joyalModel.categoryWithWeakEquivalences.weakEquivalences f
  exact hf

/-- Literal horizontal discretization and first-row evaluation form a
Quillen adjunction for the original ordinary Joyal and CSS model structures. -/
theorem isQuillenAdjunction :
    @Adjunction.IsQuillenAdjunction SSet.{0} Space _ _ joyalModel
      OrdinaryCSSLocalization.model discrete firstRow adjunction := by
  letI : discrete.PreservesCofibrations := discrete.preservesCofibrations_iff.mpr
    (fun _ _ f hf ↦ discrete_map_cofibration f hf)
  have ht : discrete.PreservesTrivialCofibrations :=
    ⟨fun _ _ f hf ↦ ⟨discrete_map_cofibration f hf.1, discrete_map_weak f hf.2⟩⟩
  letI : firstRow.PreservesFibrations :=
    adjunction.preservesTrivialCofibrations_iff_preservesFibrations.mp ht
  exact ⟨⟩

#print axioms discrete_map_cofibration
#print axioms discrete_map_weak
#print axioms isQuillenAdjunction

end
end DaggerModels.PartII.OrdinaryFirstRowQuillen
