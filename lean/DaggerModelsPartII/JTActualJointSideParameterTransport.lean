import DaggerModelsPartII.JTJointSideWhiskerParameterTransport
import DaggerModelsPartII.JTActualJointSideNativeTransport
import DaggerModelsPartII.JTActualJointCutPrism

/-! The entire original parameter on both corrected cuts is preserved by a strict cut arrow. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTActualJointSideParameterTransport

open JTParametrizedTargetFamilies (Family codes)
open JTActualJointCutPrism (leftParameter rightParameter)
open JTActualJointSideNativeTransport (leftTransport rightTransport)
open JTJointSideWhiskerParameterTransport (restrict_square append_map prepend_map)
open JTJointSideWhisker (appendParameter prependParameter)
open DaggerOriginalProductGadget (cutLeftHom cutRightHom cutLeftHom_fac cutRightHom_fac)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter

variable {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {A : Type} [SmallCategory A]
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) {a b : A} (f : a ⟶ b)
private abbrev opNative := (codes L).map f
private abbrev opDegree := (JTJointRelativeGraphFamily.coefficient (L := L)).map f
private abbrev opTime := J.map (time.map f)
variable (v : Fin (((codes L).obj a).len + 1)) (w : Fin (((codes L).obj b).len + 1))
variable (h : orderMap (opNative (L := L) f).map v = w)

/-- Exact parameter transport for the unpadded original left cut. -/
theorem left_cut_map :
    ((cutLeftHom (opNative (L := L) f) v w h).map ⊗ₘ opTime (time := time) f) ≫
      leftParameter F b w = leftParameter F a v ≫ J.map (opDegree (L := L) f) :=
  restrict_square (opTime f) (opDegree f) (F.parameter a) (F.parameter b) (opNative f).map
    (cutLeftHom (opNative f) v w h).map
    (cutLeftι ((codes L).obj a) v) (cutLeftι ((codes L).obj b) w)
    (cutLeftHom_fac (opNative f) v w h).symm (F.parameter_map f)

/-- Exact parameter transport for the unpadded original right cut. -/
theorem right_cut_map :
    ((cutRightHom (opNative (L := L) f) v w h).map ⊗ₘ opTime (time := time) f) ≫
      rightParameter F b w = rightParameter F a v ≫ J.map (opDegree (L := L) f) :=
  restrict_square (opTime f) (opDegree f) (F.parameter a) (F.parameter b) (opNative f).map
    (cutRightHom (opNative f) v w h).map
    (cutRightι ((codes L).obj a) v) (cutRightι ((codes L).obj b) w)
    (cutRightHom_fac (opNative f) v w h).symm (F.parameter_map f)

/-- The added left-cut correction edge carries the same mixed parameter square. -/
theorem left_map :
    ((leftTransport (opNative (L := L) f) v w h).map ⊗ₘ opTime (time := time) f) ≫
      appendParameter (leftParameter F b w) =
        appendParameter (leftParameter F a v) ≫ J.map (opDegree (L := L) f) :=
  append_map (cutLeftHom (opNative f) v w h) (opTime f) (opDegree f)
    (leftParameter F a v) (leftParameter F b w) (left_cut_map F f v w h)

/-- The added right-cut correction edge carries the same mixed parameter square. -/
theorem right_map :
    ((rightTransport (opNative (L := L) f) v w h).map ⊗ₘ opTime (time := time) f) ≫
      prependParameter (rightParameter F b w) =
        prependParameter (rightParameter F a v) ≫ J.map (opDegree (L := L) f) :=
  prepend_map (cutRightHom (opNative f) v w h) (opTime f) (opDegree f)
    (rightParameter F a v) (rightParameter F b w) (right_cut_map F f v w h)

end
end DaggerModels.PartII.JTActualJointSideParameterTransport
