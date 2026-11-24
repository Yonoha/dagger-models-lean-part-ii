import DaggerModelsPartII.JTGraphVariableParametrizedFamily
import DaggerModelsPartII.JTGraphVariableLabelTransport

/-! Original comma transport preserves the full parameter and native collapse equations. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphVariableParametrizedFamilyTransport

open JTGraphFactoredPresentation (TargetComma)
open JTProjectiveOrderedFiberComparison (row)
open JTGraphVariableTimeIndex (Index toNative family)
open JTGraphVariableTimeTransport (transport transport_family)
open JTGraphVariableParametrizedFamily (coherentFamily)
open JTGraphLiftTransport (GraphLift degreeOperator)
open JTGraphParameterInterpolation (interpolate)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {U V : TargetComma Q} (a : U ⟶ V) (p : Index U)

private abbrev S := ((toNative U).obj p).left
private abbrev n := (JTGraphVariableTimeIndex.degree U).obj p
private abbrev k := JTGraphLiftTransport.degree V.left

set_option maxHeartbeats 150000 in
/-- Target transport postcomposes every interpolated time parameter by
the original coefficient operator, leaving its entire source unchanged. -/
theorem parameter_transport :
    (coherentFamily V).parameter ((transport a).obj p) =
      (coherentFamily U).parameter p ≫ J.map (degreeOperator a.left) := by
  let u := fun i ↦ (family U p i).parameter
  let v := fun i ↦ (family V ((transport a).obj p) i).parameter
  let j := degreeOperator a.left
  have hv : v = fun i ↦ u i ≫ J.map j := funext fun i ↦
    congrArg GraphLift.parameter (transport_family a p i)
  have he := congrArg (fun t : Fin ((n p).len + 1) → ((S p).toSSet ⟶ J.obj (k (V := V))) ↦
    interpolate t) hv
  exact he.trans (JTInterpolatedCylinderOutput.interpolate_output j u).symm

set_option maxHeartbeats 150000 in
/-- Both collapsed native maps coincide over the original fixed target. -/
theorem collapse_transport :
    (((toNative U).obj p).hom ≫ a.left.fiber.left) ≫ V.hom.hom =
      ((toNative U).obj p).hom ≫ U.hom.hom := by
  let c := ((toNative U).obj p).hom
  have h := congrArg (fun f : (DecoratedCylinderNecklacePresentation.toTarget W x y).obj
    U.left ⟶ Q ↦ f.hom) (CostructuredArrow.w a)
  change a.left.fiber.left ≫ V.hom.hom = U.hom.hom at h
  exact (Category.assoc c a.left.fiber.left V.hom.hom).trans (congrArg (c ≫ ·) h)

end

end DaggerModels.PartII.JTGraphVariableParametrizedFamilyTransport
