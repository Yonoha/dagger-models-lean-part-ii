import DaggerModelsPartII.JTGraphVariableLiftProjections
import DaggerModelsPartII.JTGraphVariableParametrizedFamily
import DaggerModelsPartII.JTParametrizedTargetLiftProjections

/-! The coherent parameter family uses the existing two-leg pullback lift,
proved with both projections before specializing to a total resolution. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphVariableCoherentLiftComparison

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

private theorem family_decorated :
    (JTParametrizedTargetFamilies.liftNatural
        (JTGraphVariableParametrizedFamily.coherentFamily U)).app a ≫
      JTTargetCommaPullback.fst W x y Q
        ((JTGraphVariableTimeTraversal.labels U).obj a) =
      (JTGraphVariableTimeTraversal.decoratedNatural U).app a := by
  exact (JTParametrizedTargetLiftProjections.decorated
    (JTGraphVariableParametrizedFamily.coherentFamily U) a).trans (by rfl)

private theorem family_native :
    (JTParametrizedTargetFamilies.liftNatural
        (JTGraphVariableParametrizedFamily.coherentFamily U)).app a ≫
      JTTargetCommaPullback.snd W x y Q
        ((JTGraphVariableTimeTraversal.labels U).obj a) =
      (JTGraphVariableTimeTraversal.targetNatural U).app a := by
  exact (JTParametrizedTargetLiftProjections.native
    (JTGraphVariableParametrizedFamily.coherentFamily U) a).trans (by rfl)

/-- The full coherent-family lift is exactly the earlier paired lift in
both its decorated and its original native-Q projections. -/
theorem lift_app :
    (JTParametrizedTargetFamilies.liftNatural
        (JTGraphVariableParametrizedFamily.coherentFamily U)).app a =
      (JTGraphVariableTimeComparison.liftNatural U).app a := by
  apply pullback.hom_ext
    (f := (DecoratedCylinderNecklacePresentation.underCocone W x y).app
      ((JTGraphVariableTimeTraversal.labels U).obj a))
    (g := JTTargetCommaPullback.targetMap W x y Q)
  · exact (family_decorated U a).trans
      (JTGraphVariableLiftProjections.lift_fst U a).symm
  · exact (family_native U a).trans
      (JTGraphVariableLiftProjections.lift_snd U a).symm

end
end DaggerModels.PartII.JTGraphVariableCoherentLiftComparison
