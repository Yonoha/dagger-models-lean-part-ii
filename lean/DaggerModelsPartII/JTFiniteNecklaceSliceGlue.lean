import DaggerModelsPartII.JTTargetIntervalOverMapping

/-!
# Exact comparison gluing across an arbitrary native necklace joint

The common interval is the full preimage of the target joint. It may have
positive length. Every map remains over the original target necklace.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTFiniteNecklaceSliceGlue

open NecklaceCode
open JTTargetJointMarks (Joint)
open JTTargetIntervalPullback (sourceInterval)
open JTTargetIntervalGluing (leftInclusion rightInclusion)
open JTTargetIntervalOverMapping

noncomputable section

variable {U : NecklaceCode} (P : Over U) (j : Joint U)
variable (A : Over U.toSSet)

private abbrev Whole (P : Over U) := (whole U).obj P
private abbrev Left (P : Over U) (j : Joint U) := (left U j).obj P
private abbrev Right (P : Over U) (j : Joint U) := (right U j).obj P
private abbrev Overlap (P : Over U) (j : Joint U) := (overlap U j).obj P

/-- A comparison on the entire source necklace is uniquely determined by
comparisons on both inverse-image intervals agreeing on their complete
overlap. The comparison is an arrow in the slice over the original target. -/
def glue (l : Left P j ⟶ A) (r : Right P j ⟶ A)
    (h : (overlapToLeft U j).app P ≫ l =
      (overlapToRight U j).app P ≫ r) : Whole P ⟶ A :=
  (over_isPushout U j P).desc l r h

theorem glue_left (l : Left P j ⟶ A) (r : Right P j ⟶ A)
    (h : (overlapToLeft U j).app P ≫ l =
      (overlapToRight U j).app P ≫ r) :
    (leftToWhole U j).app P ≫ glue P j A l r h = l :=
  (over_isPushout U j P).inl_desc l r h

theorem glue_right (l : Left P j ⟶ A) (r : Right P j ⟶ A)
    (h : (overlapToLeft U j).app P ≫ l =
      (overlapToRight U j).app P ≫ r) :
    (rightToWhole U j).app P ≫ glue P j A l r h = r :=
  (over_isPushout U j P).inr_desc l r h

/-- The glued map carries the actual first vertex exactly as its left
interval comparison does. -/
theorem glue_first (l : Left P j ⟶ A) (r : Right P j ⟶ A)
    (h : (overlapToLeft U j).app P ≫ l =
      (overlapToRight U j).app P ≫ r) :
    pointAt P.left (ULift.up 0) ≫ (glue P j A l r h).left =
      pointAt (sourceInterval P.hom ⟨0, U.first_mem⟩ j (Fin.zero_le j.val))
        (ULift.up 0) ≫ l.left := by
  have hl := congrArg (fun f : Left P j ⟶ A ↦ f.left) (glue_left P j A l r h)
  change leftInclusion P.hom j ≫ (glue P j A l r h).left = l.left at hl
  calc
    _ = (pointAt (sourceInterval P.hom ⟨0, U.first_mem⟩ j (Fin.zero_le j.val))
          (ULift.up 0) ≫ leftInclusion P.hom j) ≫
          (glue P j A l r h).left := by
      rw [JTTargetIntervalOverMapping.left_first U j P]
    _ = _ := by rw [Category.assoc, hl]

/-- The glued map carries the actual last vertex exactly as its right
interval comparison does. -/
theorem glue_last (l : Left P j ⟶ A) (r : Right P j ⟶ A)
    (h : (overlapToLeft U j).app P ≫ l =
      (overlapToRight U j).app P ≫ r) :
    pointAt P.left (ULift.up (Fin.last P.left.len)) ≫
        (glue P j A l r h).left =
      pointAt (sourceInterval P.hom j ⟨Fin.last U.len, U.last_mem⟩
          (Fin.le_last j.val))
        (ULift.up (Fin.last
          (sourceInterval P.hom j ⟨Fin.last U.len, U.last_mem⟩
            (Fin.le_last j.val)).len)) ≫ r.left := by
  have hr := congrArg (fun f : Right P j ⟶ A ↦ f.left) (glue_right P j A l r h)
  change rightInclusion P.hom j ≫ (glue P j A l r h).left = r.left at hr
  calc
    _ = (pointAt (sourceInterval P.hom j ⟨Fin.last U.len, U.last_mem⟩
            (Fin.le_last j.val))
          (ULift.up (Fin.last
            (sourceInterval P.hom j ⟨Fin.last U.len, U.last_mem⟩
              (Fin.le_last j.val)).len)) ≫ rightInclusion P.hom j) ≫
          (glue P j A l r h).left := by
      rw [JTTargetIntervalOverMapping.right_last U j P]
    _ = _ := by rw [Category.assoc, hr]


section Diagrams

variable {B : Type} [SmallCategory B]
variable (F : B ⥤ Over U) (G : B ⥤ Over U.toSSet)
variable (l : F ⋙ left U j ⟶ G) (r : F ⋙ right U j ⟶ G)
variable (h : Functor.whiskerLeft F (overlapToLeft U j) ≫ l =
  Functor.whiskerLeft F (overlapToRight U j) ≫ r)

include h in
private theorem compatibleAt (b : B) :
    (overlapToLeft U j).app (F.obj b) ≫ l.app b =
      (overlapToRight U j).app (F.obj b) ≫ r.app b :=
  NatTrans.congr_app h b

/-- Comparisons into a varying target diagram glue over the original necklace
and retain all source and destination arrows. -/
def glueDiagram : F ⋙ whole U ⟶ G where
  app b := glue (F.obj b) j (G.obj b) (l.app b) (r.app b) (compatibleAt j F G l r h b)
  naturality {b b'} f := by
    let P := F.obj b
    let P' := F.obj b'
    let g := F.map f
    let s := over_isPushout U j P
    change (whole U).map g ≫ glue P' j (G.obj b') _ _ _ =
      glue P j (G.obj b) _ _ _ ≫ G.map f
    apply s.hom_ext
    · calc
        _ = (left U j).map g ≫ ((leftToWhole U j).app P' ≫
            glue P' j (G.obj b') _ _ _) := by
          rw [← Category.assoc, ← (leftToWhole U j).naturality g, Category.assoc]
        _ = (left U j).map g ≫ l.app b' := by rw [glue_left]
        _ = l.app b ≫ G.map f := l.naturality f
        _ = _ := by rw [← Category.assoc, glue_left]
    · calc
        _ = (right U j).map g ≫ ((rightToWhole U j).app P' ≫
            glue P' j (G.obj b') _ _ _) := by
          rw [← Category.assoc, ← (rightToWhole U j).naturality g, Category.assoc]
        _ = (right U j).map g ≫ r.app b' := by rw [glue_right]
        _ = r.app b ≫ G.map f := r.naturality f
        _ = _ := by rw [← Category.assoc, glue_right]

theorem glueDiagram_left :
    Functor.whiskerLeft F (leftToWhole U j) ≫ glueDiagram j F G l r h = l := by
  apply NatTrans.ext
  funext b
  exact glue_left (F.obj b) j (G.obj b) _ _ _

theorem glueDiagram_right :
    Functor.whiskerLeft F (rightToWhole U j) ≫ glueDiagram j F G l r h = r := by
  apply NatTrans.ext
  funext b
  exact glue_right (F.obj b) j (G.obj b) _ _ _


end Diagrams

end

end DaggerModels.PartII.JTFiniteNecklaceSliceGlue
