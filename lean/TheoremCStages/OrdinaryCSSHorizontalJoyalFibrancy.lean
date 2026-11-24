import OrdinaryHorizontalJoyalModel
import OrdinaryJoyalIsofibrationRecognition
import MatchingRestrictionCalibration
import OrdinaryCSSRestrictionQuasicategory
import OrdinaryWalkingParameterCalibration
import DaggerModelsPartII.ReedyFibrantDiagrams

/-!
# CSS fibrancy implies the actual horizontal Joyal Reedy fibrancy

The matching arrow is calibrated with the original vertical-boundary
restriction. Inner-horn and native walking-vertex lifting recognize the
original Joyal fibration class between its actual quasicategory limits.
The flipped Reedy result is then transported to the already constructed
horizontal Joyal model.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty

namespace DaggerModels.PartII.OrdinaryCSSHorizontalJoyalFibrancy

open OrdinaryCSSLocalization (Space)
open OrdinaryJTProjectiveQuillen (joyalModel)

noncomputable section

private local instance : ModelCategory SSet.{0} := joyalModel
private local instance : CategoryWithCofibrations SSet.{0} :=
  joyalModel.categoryWithCofibrations
private local instance : CategoryWithFibrations SSet.{0} := joyalModel.categoryWithFibrations
private local instance : CategoryWithWeakEquivalences SSet.{0} :=
  joyalModel.categoryWithWeakEquivalences

private abbrev reedyModel : ModelCategory Space := simplicialReedyModelCategory SSet.{0}
private local instance : ModelCategory Space := reedyModel
private local instance : CategoryWithFibrations Space := reedyModel.categoryWithFibrations
private local instance : CategoryWithCofibrations Space := reedyModel.categoryWithCofibrations
private local instance : CategoryWithWeakEquivalences Space :=
  reedyModel.categoryWithWeakEquivalences

/-- Every actual vertical monomorphism restriction of a CSS-fibrant object
is a fibration in the original Joyal model. -/
theorem restriction_joyalFibration (W : Space)
    (hW : @IsFibrant Space _ OrdinaryCSSLocalization.model.categoryWithFibrations _ W)
    {K L : SSet.{0}} (v : K ⟶ L) [Mono v] :
    joyalModel.categoryWithFibrations.fibrations (diagramRestrictionPre v W.flip) := by
  haveI := OrdinaryCSSRestrictionQuasicategory.restriction_quasicategory W hW K
  haveI := OrdinaryCSSRestrictionQuasicategory.restriction_quasicategory W hW L
  exact OrdinaryJoyalIsofibrationRecognition.originalJoyal_fibration_of_inner_and_zero
    (diagramRestrictionPre v W.flip)
    (OrdinaryCSSHorizontalRestrictions.restriction_innerFibration W hW v)
    (OrdinaryWalkingParameterCalibration.restriction_nativeWalking_lifting W hW v)

/-- The exact horizontal matching arrows of a CSS-fibrant object belong to
the original Joyal fibration class in every degree. -/
theorem matching_joyalFibration (W : Space)
    (hW : @IsFibrant Space _ OrdinaryCSSLocalization.model.categoryWithFibrations _ W)
    (n : ℕ) : fibrations SSet.{0} ((matchingComparison n).app W.flip) := by
  let v := (SSet.boundary.{0} n).ι
  have hp : fibrations SSet.{0} (diagramRestrictionPre v W.flip) :=
    restriction_joyalFibration W hW v
  let e : Arrow.mk ((matchingComparison n).app W.flip) ≅
      Arrow.mk (diagramRestrictionPre v W.flip) :=
    Arrow.isoMk (diagramRestrictionSimplexIso W.flip n).symm
      (MatchingRestrictionCalibration.matchingRestrictionIso W.flip n)
      (MatchingRestrictionCalibration.matchingRestrictionIso_comp W.flip n).symm
  exact ((fibrations SSet.{0}).arrow_mk_iso_iff e).mpr hp

/-- Flipping a CSS-fibrant object gives a Reedy-fibrant diagram with the
original Joyal coefficient model. -/
theorem flip_reedyFibrant (W : Space)
    (hW : @IsFibrant Space _ OrdinaryCSSLocalization.model.categoryWithFibrations _ W) :
    @IsFibrant Space _ reedyModel.categoryWithFibrations _ W.flip :=
  (reedyFibrant_iff_matchingComparison (C := SSet.{0}) W.flip).mpr (matching_joyalFibration W hW)

/-- CSS-fibrant objects are fibrant for the actual transported horizontal
Joyal Reedy model, with their original two simplicial indices. -/
theorem horizontal_isFibrant (W : Space)
    (hW : @IsFibrant Space _ OrdinaryCSSLocalization.model.categoryWithFibrations _ W) :
    @IsFibrant Space _ OrdinaryHorizontalJoyalModel.model.categoryWithFibrations _ W := by
  let F := (Functor.flipping : Space ≌ Space).functor
  have hR := flip_reedyFibrant W hW
  have ht : IsTerminal (F.obj (⊤_ Space)) :=
    terminalIsTerminal.isTerminalObj F (⊤_ Space)
  have hp : reedyModel.categoryWithFibrations.fibrations (F.map (terminal.from W)) :=
    (fibration_iff (C := Space) _).mp
      ((isFibrant_iff_of_isTerminal (C := Space) (F.map (terminal.from W)) ht).mp hR)
  letI : ModelCategory Space := OrdinaryHorizontalJoyalModel.model
  letI : CategoryWithFibrations Space :=
    OrdinaryHorizontalJoyalModel.model.categoryWithFibrations
  rw [isFibrant_iff, fibration_iff]
  change reedyModel.categoryWithFibrations.fibrations (F.map (terminal.from W))
  exact hp

#print axioms restriction_joyalFibration
#print axioms matching_joyalFibration
#print axioms flip_reedyFibrant
#print axioms horizontal_isFibrant

end
end DaggerModels.PartII.OrdinaryCSSHorizontalJoyalFibrancy
