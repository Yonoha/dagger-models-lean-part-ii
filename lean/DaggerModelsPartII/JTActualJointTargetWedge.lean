import ChosenNecklaceCutPushout
import ChosenNecklacesOverWedge
import DaggerModelsPartII.JTTargetJointMarks
import OriginalProductPlateau

/-! The actual target necklace splits over its own image of a joint. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace

universe u

namespace DaggerModels.PartII.JTActualJointTargetWedge

open NecklaceCode JTTargetJointMarks
open DaggerOriginalProductGadget (intervalPoint_first intervalPoint_last)

noncomputable section

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)}
variable (R : NecklacesOver X a b) (j : Joint R.code)

/-- The specified joint's image in the actual fixed target. -/
def jointVertex : X.obj (op ⦋0⦌) :=
  R.map.app _ (R.code.verticesEquiv.symm (ULift.up j.val))

/-- The literal left interval, mapped into the original target. -/
def left : NecklacesOver X a (jointVertex R j) where
  code := cutLeft R.code j.val
  map := cutLeftι R.code j.val ≫ R.map
  first := by
    change R.map.app _ ((cutLeftι R.code j.val).app _ (cutLeft R.code j.val).first) = a
    change R.map.app _ ((intervalι R.code 0 j.val (Fin.zero_le j.val)).app _
      (intervalCode R.code 0 j.val (Fin.zero_le j.val)).first) = a
    rw [intervalι_first]
    exact R.first
  last := by
    change R.map.app _ ((cutLeftι R.code j.val).app _ (cutLeft R.code j.val).last) =
      jointVertex R j
    change R.map.app _ ((intervalι R.code 0 j.val (Fin.zero_le j.val)).app _
      (intervalCode R.code 0 j.val (Fin.zero_le j.val)).last) = jointVertex R j
    rw [intervalι_last]
    rfl

/-- The literal right interval, mapped into the original target. -/
def right : NecklacesOver X (jointVertex R j) b where
  code := cutRight R.code j.val
  map := cutRightι R.code j.val ≫ R.map
  first := by
    change R.map.app _ ((cutRightι R.code j.val).app _ (cutRight R.code j.val).first) =
      jointVertex R j
    change R.map.app _ ((intervalι R.code j.val (Fin.last R.code.len) (Fin.le_last j.val)).app _
      (intervalCode R.code j.val (Fin.last R.code.len) (Fin.le_last j.val)).first) =
      jointVertex R j
    rw [intervalι_first]
    rfl
  last := by
    change R.map.app _ ((cutRightι R.code j.val).app _ (cutRight R.code j.val).last) = b
    change R.map.app _ ((intervalι R.code j.val (Fin.last R.code.len) (Fin.le_last j.val)).app _
      (intervalCode R.code j.val (Fin.last R.code.len) (Fin.le_last j.val)).last) = b
    rw [intervalι_last]
    exact R.last

/-- The unique simplicial isomorphism between the wedge and the original cut target. -/
def cutSSetIso :
    (NecklaceCode.wedge (cutLeft R.code j.val) (cutRight R.code j.val)).toSSet ≅
      R.code.toSSet :=
  (wedgeIsPushout (cutLeft R.code j.val) (cutRight R.code j.val)).isoIsPushout _ _
    (cutIsPushout R.code j.val j.property)

theorem cutSSetIso_left :
    wedgeιLeft (cutLeft R.code j.val) (cutRight R.code j.val) ≫
      (cutSSetIso R j).hom = cutLeftι R.code j.val :=
  IsPushout.inl_isoIsPushout_hom _ _ _ _

theorem cutSSetIso_right :
    wedgeιRight (cutLeft R.code j.val) (cutRight R.code j.val) ≫
      (cutSSetIso R j).hom = cutRightι R.code j.val :=
  IsPushout.inr_isoIsPushout_hom _ _ _ _

theorem cutSSetIso_first :
    pointAt (NecklaceCode.wedge (cutLeft R.code j.val) (cutRight R.code j.val))
        (ULift.up 0) ≫ (cutSSetIso R j).hom = pointAt R.code (ULift.up 0) := by
  rw [← pointAt_first_left, Category.assoc, cutSSetIso_left]
  exact intervalPoint_first R.code 0 j.val (Fin.zero_le j.val)

theorem cutSSetIso_last :
    pointAt (NecklaceCode.wedge (cutLeft R.code j.val) (cutRight R.code j.val))
        (ULift.up (Fin.last _)) ≫ (cutSSetIso R j).hom =
      pointAt R.code (ULift.up (Fin.last R.code.len)) := by
  rw [← pointAt_last_right, Category.assoc, cutSSetIso_right]
  exact intervalPoint_last R.code j.val (Fin.last R.code.len) (Fin.le_last j.val)

theorem cutSSetIso_map :
    (cutSSetIso R j).hom ≫ R.map =
      (NecklacesOver.wedge (left R j) (right R j)).map := by
  apply (wedgeIsPushout (cutLeft R.code j.val) (cutRight R.code j.val)).hom_ext
  · rw [← Category.assoc, cutSSetIso_left]
    exact (NecklacesOver.wedge_left (left R j) (right R j)).symm
  · rw [← Category.assoc, cutSSetIso_right]
    exact (NecklacesOver.wedge_right (left R j) (right R j)).symm

/-- The canonical comparison is an isomorphism of actual over-target necklaces. -/
def cutIso : NecklacesOver.wedge (left R j) (right R j) ≅ R where
  hom := {
    hom := {
      map := (cutSSetIso R j).hom
      first := first_of_point _ (cutSSetIso_first R j)
      last := last_of_point _ (cutSSetIso_last R j) }
    w := cutSSetIso_map R j }
  inv := {
    hom := {
      map := (cutSSetIso R j).inv
      first := first_of_point _ (((cutSSetIso R j).comp_inv_eq).2
        (cutSSetIso_first R j).symm)
      last := last_of_point _ (((cutSSetIso R j).comp_inv_eq).2
        (cutSSetIso_last R j).symm) }
    w := by
      change (cutSSetIso R j).inv ≫
        (NecklacesOver.wedge (left R j) (right R j)).map = R.map
      rw [← cutSSetIso_map, ← Category.assoc, Iso.inv_hom_id, Category.id_comp] }
  hom_inv_id := by
    apply NecklacesOver.Hom.ext
    apply NecklaceCode.Hom.ext
    exact (cutSSetIso R j).hom_inv_id
  inv_hom_id := by
    apply NecklacesOver.Hom.ext
    apply NecklaceCode.Hom.ext
    exact (cutSSetIso R j).inv_hom_id

theorem cutIso_left :
    wedgeιLeft (cutLeft R.code j.val) (cutRight R.code j.val) ≫
      (cutIso R j).hom.hom.map = cutLeftι R.code j.val :=
  cutSSetIso_left R j

theorem cutIso_right :
    wedgeιRight (cutLeft R.code j.val) (cutRight R.code j.val) ≫
      (cutIso R j).hom.hom.map = cutRightι R.code j.val :=
  cutSSetIso_right R j

end

end DaggerModels.PartII.JTActualJointTargetWedge
