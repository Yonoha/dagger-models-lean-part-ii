import DaggerModelsPartII.JTGraphVariableTimeComparison

/-! Expose the two existing pointwise pullback projections before specializing
an original object to the total variable-source resolution. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphVariableLiftProjections

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable (U : TargetComma Q) (a : JTGraphVariableTimeIndex.Index U)

private abbrev i := (JTGraphVariableTimeTraversal.labels U).obj a
private abbrev fstMap :=
  (DecoratedCylinderNecklacePresentation.underCocone W x y).app (i U a)
private abbrev sndMap := JTTargetCommaPullback.targetMap W x y Q

/-- The old pointwise lift has the prescribed complete decorated leg. -/
theorem lift_fst :
    (JTGraphVariableTimeComparison.liftNatural U).app a ≫
        JTTargetCommaPullback.fst W x y Q (i U a) =
      (JTGraphVariableTimeTraversal.decoratedNatural U).app a := by
  let hp := IsPullback.of_hasPullback (fstMap U a) (sndMap (Q := Q))
  change hp.lift ((JTGraphVariableTimeTraversal.decoratedNatural U).app a)
      ((JTGraphVariableTimeTraversal.targetNatural U).app a)
      (JTGraphVariableTimeTraversal.pair_square U a) ≫ _ = _
  exact hp.lift_fst _ _ _

/-- Its native leg retains the entire original fixed-target map. -/
theorem lift_snd :
    (JTGraphVariableTimeComparison.liftNatural U).app a ≫
        JTTargetCommaPullback.snd W x y Q (i U a) =
      (JTGraphVariableTimeTraversal.targetNatural U).app a := by
  let hp := IsPullback.of_hasPullback (fstMap U a) (sndMap (Q := Q))
  change hp.lift ((JTGraphVariableTimeTraversal.decoratedNatural U).app a)
      ((JTGraphVariableTimeTraversal.targetNatural U).app a)
      (JTGraphVariableTimeTraversal.pair_square U a) ≫ _ = _
  exact hp.lift_snd _ _ _

end
end DaggerModels.PartII.JTGraphVariableLiftProjections
