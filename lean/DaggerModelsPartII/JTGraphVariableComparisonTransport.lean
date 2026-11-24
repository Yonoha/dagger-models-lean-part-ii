import DaggerModelsPartII.JTGraphVariableTimeComparison
import DaggerModelsPartII.JTGraphVariableLabelTransport

/-! Transport of the complete comparison along original comma arrows. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphVariableComparisonTransport

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphVariableTimeIndex
open JTGraphVariableTimeTransport (transport transport_family transportResolution)
open JTGraphVariableTimeTraversal (labels cylinders decoratedNatural targetNatural)
open JTGraphVariableTimeComparison (toComma liftNatural lift_fst lift_snd square_of_projections)
open JTGraphVariableLabelTransport (labelTransport labelTransport_projection)
open JTGraphLiftTransport (degreeOperator projection)
open JTNecklaceEndpointCylinder (nativeMap value)
open JTGraphParameterInterpolation (interpolate)
open JTInterpolatedReducedCylinder (cylinderMap)
open NecklaceCylinderAugmentation (augmentation)
open DecoratedCylinderNecklacePresentation (underDiagram underCocone toTarget)
open BoundaryNecklaceComma (fiberDiagram)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {U V : TargetComma Q} (a : U ⟶ V)

private abbrev E := JTTargetCommaPullback.diagram W x y Q

private theorem decorated_square (P : Index U) :
    (decoratedNatural U).app P ≫ (underDiagram W x y).map ((labelTransport a).app P) =
      (decoratedNatural V).app ((transport a).obj P) := by
  let S := ((toNative U).obj P).left
  let p := fun i ↦ (family U P i).parameter
  apply Under.UnderMorphism.ext
  change cylinderMap S (interpolate p) ≫
    (NecklaceCylinderJointDiagram.cylinderUnder.map
      ((projection (W := W) (x := x) (y := y)).map ((labelTransport a).app P))).right = _
  rw [labelTransport_projection a P]
  change cylinderMap S (interpolate p) ≫
      (nativeMap (𝟙 S) (JTGraphLiftTransport.degree U.left) ≫
        (value S).map (degreeOperator a.left)) =
    cylinderMap S (interpolate (fun i ↦ (family V ((transport a).obj P) i).parameter))
  rw [JTNecklaceEndpointCylinder.nativeMap_id, Category.id_comp]
  have h := (JTInterpolatedCylinderOutput.interpolated_output S (degreeOperator a.left) p).2
  refine h.trans ?_
  have hp : (fun i ↦ p i ≫ GroupoidSimplex.parameter.map (degreeOperator a.left)) =
      (fun i ↦ (family V ((transport a).obj P) i).parameter) := by
    funext i
    exact (congrArg JTGraphLiftTransport.GraphLift.parameter (transport_family a P i)).symm
  exact congrArg (fun s ↦ cylinderMap S (interpolate s)) hp

private theorem native_square (P : Index U) :
    (targetNatural U).app P = (targetNatural V).app ((transport a).obj P) := by
  let S := ((toNative U).obj P).left
  let c := ((toNative U).obj P).hom
  let n := (degree U).obj P
  have hw := congrArg (fun f : (toTarget W x y).obj U.left ⟶ Q ↦ f.hom)
    (CostructuredArrow.w a)
  change a.left.fiber.left ≫ V.hom.hom = U.hom.hom at hw
  have hh : c ≫ U.hom.hom = (c ≫ a.left.fiber.left) ≫ V.hom.hom := by
    rw [Category.assoc, hw]
  apply Under.UnderMorphism.ext
  change augmentation S n ≫ (c ≫ U.hom.hom).map =
    augmentation S n ≫ ((c ≫ a.left.fiber.left) ≫ V.hom.hom).map
  exact congrArg (fun f : S ⟶ Q.code ↦ augmentation S n ≫ f.map) hh

/-- The two projections identify the exact lift after original target transport. -/
theorem lift_square (P : Index U) :
    (liftNatural U).app P ≫ (E (Q := Q)).map ((labelTransport a).app P) =
      (liftNatural V).app ((transport a).obj P) := by
  let i := (labels U).obj P
  let j := (labels V).obj ((transport a).obj P)
  let v := (labelTransport a).app P
  let q := (liftNatural V).app ((transport a).obj P)
  have hp := IsPullback.of_hasPullback ((underCocone W x y).app j)
    (JTTargetCommaPullback.targetMap W x y Q)
  have hf := JTTargetCommaPullback.map_fst W x y Q (i := i) (j := j) v
  have hs := JTTargetCommaPullback.map_snd W x y Q (i := i) (j := j) v
  have h₁ := (congrArg (· ≫ (underDiagram W x y).map v) (lift_fst U P)).trans
    (decorated_square a P)
  have h₂ := (lift_snd U P).trans (native_square a P)
  have he : (liftNatural U).app P ≫ (E (Q := Q)).map v = 𝟙 _ ≫ q :=
    square_of_projections hp hf hs (lift_fst V ((transport a).obj P))
      (lift_snd V ((transport a).obj P)) (h₁.trans (Category.id_comp _).symm)
      (h₂.trans (Category.id_comp _).symm)
  exact he.trans (Category.id_comp q)

set_option maxHeartbeats 95000 in
/-- The same lift square with the cylinder source read in the two different diagrams. -/
theorem lift_square_heq (P : Index U) :
    HEq ((liftNatural U).app P ≫ (E (Q := Q)).map ((labelTransport a).app P))
      ((liftNatural V).app ((transport a).obj P)) := by
  have h := @lift_square W x y Q U V a P
  exact heq_of_eq h

end
end DaggerModels.PartII.JTGraphVariableComparisonTransport
