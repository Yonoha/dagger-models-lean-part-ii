import OrdinaryJTProjectiveQuillen
import NativeInnerQuasicategoryWeakReplacement

/-!
# Fibrancy for the original ordinary Joyal model

The original Smith fibration class is the literal lifting candidate.
`candidate_terminal_quasicategory` and `terminal_candidate` already prove
both directions of its terminal-object characterization. The explicit
model in the statement keeps it separate from the native Kan coefficients.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits HomotopicalAlgebra

namespace DaggerModels.PartII.OrdinaryJoyalFibrancy

open OrdinaryJTProjectiveQuillen (joyalModel)

noncomputable section

private local instance : ModelCategory SSet.{0} := joyalModel
private local instance : CategoryWithCofibrations SSet.{0} :=
  joyalModel.categoryWithCofibrations
private local instance : CategoryWithFibrations SSet.{0} :=
  joyalModel.categoryWithFibrations
private local instance : CategoryWithWeakEquivalences SSet.{0} :=
  joyalModel.categoryWithWeakEquivalences

/-- The original ordinary Joyal fibrant objects are precisely the quasicategories. -/
theorem isFibrant_iff_quasicategory (X : SSet.{0}) :
    @IsFibrant SSet.{0} _ joyalModel.categoryWithFibrations _ X ↔ X.Quasicategory := by
  rw [isFibrant_iff, fibration_iff]
  change joyalModel.categoryWithFibrations.fibrations (terminal.from X) ↔ X.Quasicategory
  rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelFib,
    DaggerNativeFullWeakSmithGenerators.boundary_cof]
  constructor
  · intro h
    exact DaggerNativeInnerQuasicategoryWeakReplacement.candidate_terminal_quasicategory
      (terminal.from X) terminalIsTerminal h
  · intro h
    letI : X.Quasicategory := h
    exact DaggerNativeJoyalWeakTrivialFibrationSpan.terminal_candidate X

#print axioms isFibrant_iff_quasicategory

end

end DaggerModels.PartII.OrdinaryJoyalFibrancy
