import DaggerModelsPartII.JTGraphVariableTimeTransport
import DaggerModelsPartII.JTGraphVariableTimeTraversal

/-! The joint source and time diagram is unchanged by original target transport. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphVariableCylinderTransport

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphVariableTimeIndex (Index joint)
open JTGraphVariableTimeTransport (transport transport_joint)
open JTGraphVariableTimeTraversal (cylinders)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {U V : TargetComma Q} (a : U ⟶ V)

private theorem whisker_eq {A B C D : Type*} [Category* A] [Category* B]
    [Category* C] [Category* D] (f : A ⥤ B) (g : B ⥤ C) (k : A ⥤ C)
    (u : C ⥤ D) (h : f ⋙ g = k) : f ⋙ g ⋙ u = k ⋙ u :=
  (Functor.assoc f g u).symm.trans (congrArg (· ⋙ u) h)

private theorem eqToHom_eq_id {C : Type*} [Category C] {X : C} (h : X = X) :
    eqToHom h = 𝟙 X := by cases h; rfl

private abbrev indexAt (A : TargetComma Q) := @Index W x y Q A
private abbrev jointAt (A : TargetComma Q) := @joint W x y Q A
private abbrev cylinderAt (A : TargetComma Q) := @cylinders W x y Q A
private abbrev transportIndex := @transport W x y Q U V a

/-- Cylinder reindexing preserves both operators of the joint diagram. -/
theorem cylinders_eq : transportIndex a ⋙ cylinderAt V = cylinderAt U :=
  @whisker_eq (indexAt U) (indexAt V) (NecklaceCode × SimplexCategory)
    (Under JTXiEndpointCollapse.boundary) _ _ _ _
    (transportIndex a) (jointAt V) (jointAt U) NecklaceCylinderJointDiagram.cylinderUnder
    (@transport_joint W x y Q U V a)

private abbrev BoundaryCylinder := Under JTXiEndpointCollapse.boundary

set_option maxHeartbeats 85000 in
/-- The reindexing equality has identity component at every original cylinder. -/
theorem cylinders_eq_app (P : @Index W x y Q U) :
    (eqToHom (@cylinders_eq W x y Q U V a).symm).app P =
      𝟙 ((@cylinders W x y Q U).obj P) := by
  let F := @cylinders W x y Q U
  let G := @transport W x y Q U V a ⋙ @cylinders W x y Q V
  let h : F = G := (@cylinders_eq W x y Q U V a).symm
  exact (@eqToHom_app (@Index W x y Q U) _ BoundaryCylinder _ F G h P).trans
    (@eqToHom_eq_id BoundaryCylinder _ (F.obj P) (Functor.congr_obj h P))

end
end DaggerModels.PartII.JTGraphVariableCylinderTransport
