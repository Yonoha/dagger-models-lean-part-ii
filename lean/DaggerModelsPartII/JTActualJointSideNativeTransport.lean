import DaggerModelsPartII.JTActualJointSideWhiskerNative
import OriginalCutMapLaws

/-! Transport of the whiskered actual-joint sides along cut-preserving source arrows. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTActualJointSideNativeTransport

open NecklaceCode
open JTTargetJointMarks (Joint)
open JTActualJointSideWhiskerNative
open DaggerOriginalProductGadget

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Input (W : Source) := JTReversalInput.ordinaryInput.obj W
private abbrev Raw (W : Source) := OrdinaryJTRealization.realization.obj (Input W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : Vertex W}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)) (j : Joint Q.code)
variable {S S' : NecklaceCode} (g : NecklaceCode.Hom.{0} S S')
variable (f' : NecklaceCode.Hom.{0} S' Q.code)
variable (v : Fin (S.len + 1)) (v' : Fin (S'.len + 1))
variable (hg : orderMap g.map v = v') (hv' : orderMap f'.map v' = j.val)

private abbrev hcomp := cutJoint_comp g f' v v' j.val hg hv'

/-- Cut-preserving transport with identity on the added ending bead. -/
def leftTransport : wedge (cutLeft S v) (single 1) ⟶
    wedge (cutLeft S' v') (single 1) :=
  wedgeMap (cutLeftHom g v v' hg) (𝟙 (single 1))

/-- Cut-preserving transport with identity on the added preceding bead. -/
def rightTransport : wedge (single 1) (cutRight S v) ⟶
    wedge (single 1) (cutRight S' v') :=
  wedgeMap (𝟙 (single 1)) (cutRightHom g v v' hg)

/-- Identity source arrows induce identity transport on the left whiskered cut. -/
theorem leftTransport_id (T : NecklaceCode) (w : Fin (T.len + 1)) :
    leftTransport (NecklaceCode.Hom.id.{0} T) w w (orderMap_id_apply T w) =
      𝟙 (wedge (cutLeft T w) (single 1)) := by
  change wedgeMap (cutLeftHom (NecklaceCode.Hom.id T) w w (orderMap_id_apply T w))
      (NecklaceCode.Hom.id (single 1)) = NecklaceCode.Hom.id _
  rw [cutLeftHom_id, wedgeMap_id]

/-- Identity source arrows induce identity transport on the right whiskered cut. -/
theorem rightTransport_id (T : NecklaceCode) (w : Fin (T.len + 1)) :
    rightTransport (NecklaceCode.Hom.id.{0} T) w w (orderMap_id_apply T w) =
      𝟙 (wedge (single 1) (cutRight T w)) := by
  change wedgeMap (NecklaceCode.Hom.id (single 1))
      (cutRightHom (NecklaceCode.Hom.id T) w w (orderMap_id_apply T w)) =
        NecklaceCode.Hom.id _
  rw [cutRightHom_id, wedgeMap_id]

/-- Left transport commutes with restriction to the actual left target. -/
theorem leftNative_comp :
    leftTransport g v v' hg ≫ leftNative Q j f' v' hv' =
      leftNative Q j (NecklaceCode.Hom.comp g f') v
        (hcomp Q j g f' v v' hg hv') := by
  apply NecklaceCode.Hom.ext
  apply (wedgeIsPushout (cutLeft S v) (single 1)).hom_ext
  · change wedgeιLeft _ _ ≫ (leftTransport g v v' hg).map ≫
        (leftNative Q j f' v' hv').map = _
    change (wedgeιLeft _ _ ≫ (wedgeMap (cutLeftHom g v v' hg) (𝟙 (single 1))).map) ≫
      (leftNative Q j f' v' hv').map = _
    rw [wedgeMap_left, Category.assoc,
      leftNative_interior, leftNative_interior]
    exact congrArg NecklaceCode.Hom.map
      (cutLeftHom_comp g f' v v' j.val hg hv').symm
  · change wedgeιRight _ _ ≫ (leftTransport g v v' hg).map ≫
        (leftNative Q j f' v' hv').map = _
    change (wedgeιRight _ _ ≫ (wedgeMap (cutLeftHom g v v' hg) (𝟙 (single 1))).map) ≫
      (leftNative Q j f' v' hv').map = _
    rw [wedgeMap_right]
    change ((𝟙 ((single 1).toSSet)) ≫ wedgeιRight _ _) ≫
      (leftNative Q j f' v' hv').map = _
    rw [Category.id_comp,
      leftNative_whisker, leftNative_whisker]

/-- Right transport commutes with restriction to the actual right target. -/
theorem rightNative_comp :
    rightTransport g v v' hg ≫ rightNative Q j f' v' hv' =
      rightNative Q j (NecklaceCode.Hom.comp g f') v
        (hcomp Q j g f' v v' hg hv') := by
  apply NecklaceCode.Hom.ext
  apply (wedgeIsPushout (single 1) (cutRight S v)).hom_ext
  · change wedgeιLeft _ _ ≫ (rightTransport g v v' hg).map ≫
        (rightNative Q j f' v' hv').map = _
    change (wedgeιLeft _ _ ≫ (wedgeMap (𝟙 (single 1)) (cutRightHom g v v' hg)).map) ≫
      (rightNative Q j f' v' hv').map = _
    rw [wedgeMap_left]
    change ((𝟙 ((single 1).toSSet)) ≫ wedgeιLeft _ _) ≫
      (rightNative Q j f' v' hv').map = _
    rw [Category.id_comp,
      rightNative_whisker, rightNative_whisker]
  · change wedgeιRight _ _ ≫ (rightTransport g v v' hg).map ≫
        (rightNative Q j f' v' hv').map = _
    change (wedgeιRight _ _ ≫ (wedgeMap (𝟙 (single 1)) (cutRightHom g v v' hg)).map) ≫
      (rightNative Q j f' v' hv').map = _
    rw [wedgeMap_right, Category.assoc,
      rightNative_interior, rightNative_interior]
    exact congrArg NecklaceCode.Hom.map
      (cutRightHom_comp g f' v v' j.val hg hv').symm

/-- The left transport is an endpoint-ordered arrow over the original raw target. -/
def leftTransportOver :
    leftSource Q j (NecklaceCode.Hom.comp g f') v (hcomp Q j g f' v v' hg hv') ⟶
      leftSource Q j f' v' hv' where
  hom := leftTransport g v v' hg
  w := by
    change (leftTransport g v v' hg).map ≫
      ((leftNative Q j f' v' hv').map ≫
        (JTActualJointMarkedEvaluation.left Q j).map) =
      (leftNative Q j (NecklaceCode.Hom.comp g f') v
        (hcomp Q j g f' v v' hg hv')).map ≫
        (JTActualJointMarkedEvaluation.left Q j).map
    exact congrArg (· ≫ (JTActualJointMarkedEvaluation.left Q j).map)
      (congrArg NecklaceCode.Hom.map (leftNative_comp Q j g f' v v' hg hv'))

/-- The right transport is an endpoint-ordered arrow over the original raw target. -/
def rightTransportOver :
      rightSource Q j (NecklaceCode.Hom.comp g f') v (hcomp Q j g f' v v' hg hv') ⟶
      rightSource Q j f' v' hv' where
  hom := rightTransport g v v' hg
  w := by
    change (rightTransport g v v' hg).map ≫
      ((rightNative Q j f' v' hv').map ≫
        (JTActualJointMarkedEvaluation.right Q j).map) =
      (rightNative Q j (NecklaceCode.Hom.comp g f') v
        (hcomp Q j g f' v v' hg hv')).map ≫
        (JTActualJointMarkedEvaluation.right Q j).map
    exact congrArg (· ≫ (JTActualJointMarkedEvaluation.right Q j).map)
      (congrArg NecklaceCode.Hom.map (rightNative_comp Q j g f' v v' hg hv'))

end
end DaggerModels.PartII.JTActualJointSideNativeTransport
