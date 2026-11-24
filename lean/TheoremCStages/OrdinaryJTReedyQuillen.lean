import OrdinaryJTProjectiveQuillen

/-!
# The actual ordinary JT Quillen adjunction for the Kan Reedy model

The checked native relative matching theorem supplies all Reedy fibrations.
For an original Joyal trivial fibration, the checked projective result also
supplies levelwise Kan weakness, which is the Reedy weak-equivalence class.
The same categorical adjunction is therefore Quillen before localization.
No complete-Segal-space Quillen equivalence or unit weakness is asserted.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryJTReedyQuillen

open OrdinaryJTCurriedAdjunction
open OrdinaryJTProjectiveQuillen (joyalModel)

noncomputable section

/-- The native Kan Reedy model on the actual ordinary simplicial spaces. -/
def diagramModel : ModelCategory (SimplexCategoryᵒᵖ ⥤ SSet.{0}) :=
  simplicialReedyModelCategory SSet.{0}

/-- The actual right adjoint preserves full Reedy fibrations. -/
theorem right_map_fibration {X Y : SSet.{0}} (p : X ⟶ Y)
    (hp : joyalModel.categoryWithFibrations.fibrations p) :
    diagramModel.categoryWithFibrations.fibrations (right.map p) :=
  OrdinaryJTNativeMapReedy.right_map_relativeReedyFibration p hp

/-- Original Joyal trivial fibrations become full Reedy trivial fibrations. -/
theorem right_map_trivialFibration {X Y : SSet.{0}} (p : X ⟶ Y)
    (hp : joyalModel.categoryWithFibrations.fibrations p)
    (hw : (joyalModel.categoryWithWeakEquivalences).weakEquivalences p) :
    diagramModel.categoryWithFibrations.fibrations (right.map p) ∧
      diagramModel.categoryWithWeakEquivalences.weakEquivalences (right.map p) :=
  ⟨right_map_fibration p hp,
    (OrdinaryJTProjectiveQuillen.right_map_trivialFibration p hp hw).2⟩

/-- The original curried JT realization--nerve adjunction is Quillen for the
native Kan Reedy model and the original ordinary Joyal model. -/
theorem isQuillenAdjunction :
    @Adjunction.IsQuillenAdjunction (SimplexCategoryᵒᵖ ⥤ SSet.{0}) SSet.{0}
      _ _ diagramModel joyalModel left right adjunction := by
  let M := joyalModel
  letI : ModelCategory (SimplexCategoryᵒᵖ ⥤ SSet.{0}) := diagramModel
  letI : ModelCategory SSet.{0} := M
  letI : CategoryWithFibrations SSet.{0} := M.categoryWithFibrations
  letI : CategoryWithCofibrations SSet.{0} := M.categoryWithCofibrations
  letI : CategoryWithWeakEquivalences SSet.{0} := M.categoryWithWeakEquivalences
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

end DaggerModels.PartII.OrdinaryJTReedyQuillen
