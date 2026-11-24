import DaggerModelsPartII.JTActualJointMarkedEvaluation
import DaggerModelsPartII.JTOrderedLabelJointInsertion
import OriginalNecklaceCutMaps

/-! Native side restrictions with an inserted bead collapsed at an actual target joint. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTActualJointSideWhiskerNative

open NecklaceCode
open JTTargetJointMarks (Joint)
open DaggerOriginalProductGadget (cutLeftHom cutRightHom cutLeftHom_fac cutRightHom_fac)
open DaggerOriginalProductGadget (intervalPoint_first intervalPoint_last)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Input (W : Source) := JTReversalInput.ordinaryInput.obj W
private abbrev Raw (W : Source) := OrdinaryJTRealization.realization.obj (Input W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : Vertex W}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)) (j : Joint Q.code)
variable {S : NecklaceCode} (f : NecklaceCode.Hom.{0} S Q.code)
variable (v : Fin (S.len + 1)) (hv : orderMap f.map v = j.val)

/-- The left source cut followed by one bead, with that bead collapsed at the joint. -/
def leftNative :
    wedge (cutLeft S v) (single 1) ⟶ (JTActualJointMarkedEvaluation.left Q j).code :=
  wedgeMap (cutLeftHom f v j.val hv)
      (JTOrderedLabelJointInsertion.toPoint (single 1)) ≫
    wedgeRightUnitCode (cutLeft Q.code j.val)

@[reassoc]
theorem leftNative_interior :
    wedgeιLeft (cutLeft S v) (single 1) ≫ (leftNative Q j f v hv).map =
      (cutLeftHom f v j.val hv).map := by
  change wedgeιLeft _ _ ≫ (wedgeMap _ _).map ≫ (wedgeRightUnitCode _).map = _
  rw [← Category.assoc, wedgeMap_left, Category.assoc]
  exact (wedgeRightUnit.{0} (cutLeft Q.code j.val)).inv_hom_id ▸ rfl

@[reassoc]
theorem leftNative_whisker :
    wedgeιRight (cutLeft S v) (single 1) ≫ (leftNative Q j f v hv).map =
      (JTOrderedLabelJointInsertion.toPoint (single 1)).map ≫
        pointAt (cutLeft Q.code j.val) (ULift.up (Fin.last (cutLeft Q.code j.val).len)) := by
  change wedgeιRight _ _ ≫ (wedgeMap _ _).map ≫ (wedgeRightUnitCode _).map = _
  rw [← Category.assoc, wedgeMap_right, Category.assoc]
  exact congrArg ((JTOrderedLabelJointInsertion.toPoint (single 1)).map ≫ ·)
    (wedgeRightUnit_point (cutLeft Q.code j.val))

/-- The right source cut preceded by one bead, with that bead collapsed at the joint. -/
def rightNative :
    wedge (single 1) (cutRight S v) ⟶ (JTActualJointMarkedEvaluation.right Q j).code :=
  wedgeMap (JTOrderedLabelJointInsertion.toPoint (single 1))
      (cutRightHom f v j.val hv) ≫
    wedgeLeftUnitCode (cutRight Q.code j.val)

@[reassoc]
theorem rightNative_whisker :
    wedgeιLeft (single 1) (cutRight S v) ≫ (rightNative Q j f v hv).map =
      (JTOrderedLabelJointInsertion.toPoint (single 1)).map ≫
        pointAt (cutRight Q.code j.val) (ULift.up 0) := by
  change wedgeιLeft _ _ ≫ (wedgeMap _ _).map ≫ (wedgeLeftUnitCode _).map = _
  rw [← Category.assoc, wedgeMap_left, Category.assoc]
  exact congrArg ((JTOrderedLabelJointInsertion.toPoint (single 1)).map ≫ ·)
    (wedgeLeftUnit_point (cutRight Q.code j.val))

@[reassoc]
theorem rightNative_interior :
    wedgeιRight (single 1) (cutRight S v) ≫ (rightNative Q j f v hv).map =
      (cutRightHom f v j.val hv).map := by
  change wedgeιRight _ _ ≫ (wedgeMap _ _).map ≫ (wedgeLeftUnitCode _).map = _
  rw [← Category.assoc, wedgeMap_right, Category.assoc]
  exact (wedgeLeftUnit.{0} (cutRight Q.code j.val)).inv_hom_id ▸ rfl

/-- The interior of the left whiskered source retains its literal original raw map. -/
@[reassoc]
theorem left_raw_interior :
    wedgeιLeft (cutLeft S v) (single 1) ≫ (leftNative Q j f v hv).map ≫
      (JTActualJointMarkedEvaluation.left Q j).map =
      cutLeftι S v ≫ f.map ≫ Q.map := by
  rw [← Category.assoc, leftNative_interior]
  change (cutLeftHom f v j.val hv).map ≫ (cutLeftι Q.code j.val ≫ Q.map) = _
  rw [← Category.assoc, cutLeftHom_fac, Category.assoc]

/-- The ending bead is constant at the actual joint in the fixed raw target. -/
@[reassoc]
theorem left_raw_whisker :
    wedgeιRight (cutLeft S v) (single 1) ≫ (leftNative Q j f v hv).map ≫
      (JTActualJointMarkedEvaluation.left Q j).map =
      (JTOrderedLabelJointInsertion.toPoint (single 1)).map ≫
        pointAt Q.code (ULift.up j.val) ≫ Q.map := by
  rw [← Category.assoc, leftNative_whisker]
  change ((JTOrderedLabelJointInsertion.toPoint (single 1)).map ≫
      pointAt (cutLeft Q.code j.val) (ULift.up (Fin.last _))) ≫
      (cutLeftι Q.code j.val ≫ Q.map) = _
  simpa only [Category.assoc] using
    congrArg (fun h : (Δ[0] : SSet.{0}) ⟶ Q.code.toSSet ↦
      (JTOrderedLabelJointInsertion.toPoint (single 1)).map ≫ h ≫ Q.map)
      (intervalPoint_last Q.code 0 j.val (Fin.zero_le j.val))

/-- The preceding bead is constant at the same actual joint. -/
@[reassoc]
theorem right_raw_whisker :
    wedgeιLeft (single 1) (cutRight S v) ≫ (rightNative Q j f v hv).map ≫
      (JTActualJointMarkedEvaluation.right Q j).map =
      (JTOrderedLabelJointInsertion.toPoint (single 1)).map ≫
        pointAt Q.code (ULift.up j.val) ≫ Q.map := by
  rw [← Category.assoc, rightNative_whisker]
  change ((JTOrderedLabelJointInsertion.toPoint (single 1)).map ≫
      pointAt (cutRight Q.code j.val) (ULift.up 0)) ≫
      (cutRightι Q.code j.val ≫ Q.map) = _
  simpa only [Category.assoc] using
    congrArg (fun h : (Δ[0] : SSet.{0}) ⟶ Q.code.toSSet ↦
      (JTOrderedLabelJointInsertion.toPoint (single 1)).map ≫ h ≫ Q.map)
      (intervalPoint_first Q.code j.val (Fin.last Q.code.len) (Fin.le_last j.val))

/-- The interior of the right whiskered source retains its literal original raw map. -/
@[reassoc]
theorem right_raw_interior :
    wedgeιRight (single 1) (cutRight S v) ≫ (rightNative Q j f v hv).map ≫
      (JTActualJointMarkedEvaluation.right Q j).map =
      cutRightι S v ≫ f.map ≫ Q.map := by
  rw [← Category.assoc, rightNative_interior]
  change (cutRightHom f v j.val hv).map ≫ (cutRightι Q.code j.val ≫ Q.map) = _
  rw [← Category.assoc, cutRightHom_fac, Category.assoc]

/-- The whiskered left source, with the actual raw map determined by the native arrow. -/
def leftSource : NecklacesOver (Raw W) (rawVertex W x)
    (rawVertex W (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)) where
  code := wedge (cutLeft S v) (single 1)
  map := (leftNative Q j f v hv).map ≫ (JTActualJointMarkedEvaluation.left Q j).map
  first := by
    change (JTActualJointMarkedEvaluation.left Q j).map.app _
      ((leftNative Q j f v hv).map.app _ (wedge (cutLeft S v) (single 1)).first) = _
    rw [(leftNative Q j f v hv).first]
    exact (JTActualJointMarkedEvaluation.left Q j).first
  last := by
    change (JTActualJointMarkedEvaluation.left Q j).map.app _
      ((leftNative Q j f v hv).map.app _ (wedge (cutLeft S v) (single 1)).last) = _
    rw [(leftNative Q j f v hv).last]
    exact (JTActualJointMarkedEvaluation.left Q j).last

/-- The literal endpoint-ordered map to the actual left target. -/
def leftHom : leftSource Q j f v hv ⟶ JTActualJointMarkedEvaluation.left Q j where
  hom := leftNative Q j f v hv
  w := rfl

/-- The whiskered right source, with the actual raw map determined by the native arrow. -/
def rightSource : NecklacesOver (Raw W)
    (rawVertex W (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)) (rawVertex W y) where
  code := wedge (single 1) (cutRight S v)
  map := (rightNative Q j f v hv).map ≫ (JTActualJointMarkedEvaluation.right Q j).map
  first := by
    change (JTActualJointMarkedEvaluation.right Q j).map.app _
      ((rightNative Q j f v hv).map.app _ (wedge (single 1) (cutRight S v)).first) = _
    rw [(rightNative Q j f v hv).first]
    exact (JTActualJointMarkedEvaluation.right Q j).first
  last := by
    change (JTActualJointMarkedEvaluation.right Q j).map.app _
      ((rightNative Q j f v hv).map.app _ (wedge (single 1) (cutRight S v)).last) = _
    rw [(rightNative Q j f v hv).last]
    exact (JTActualJointMarkedEvaluation.right Q j).last

/-- The literal endpoint-ordered map to the actual right target. -/
def rightHom : rightSource Q j f v hv ⟶ JTActualJointMarkedEvaluation.right Q j where
  hom := rightNative Q j f v hv
  w := rfl

/-- Every native collapse has an actual source joint above the chosen target joint. -/
theorem exists_sourceJoint :
    ∃ w : Joint S, orderMap f.map w.val = j.val := by
  obtain ⟨m, hm⟩ := JTTargetJointMarks.exists_joint_marks f
  exact ⟨⟨(m j).val, hm j⟩, (m j).property⟩

variable {A : Type} [SmallCategory A]
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory}

/-- An actual family gives the left map at every chosen source joint above `j`. -/
abbrev leftAt (F : JTParametrizedTargetFamilies.Family Q L time) (a : A)
    (v : Joint ((JTParametrizedTargetFamilies.codes L).obj a))
    (hv : orderMap (F.collapse.app a).map v.val = j.val) :=
  leftHom Q j (F.collapse.app a) v.val hv

/-- An actual family gives the right map at every chosen source joint above `j`. -/
abbrev rightAt (F : JTParametrizedTargetFamilies.Family Q L time) (a : A)
    (v : Joint ((JTParametrizedTargetFamilies.codes L).obj a))
    (hv : orderMap (F.collapse.app a).map v.val = j.val) :=
  rightHom Q j (F.collapse.app a) v.val hv

end
end DaggerModels.PartII.JTActualJointSideWhiskerNative
