import DaggerModelsPartII.JTJointClippedSides
import DaggerModelsPartII.JTJointIntervalQuotient
import ChosenNecklaceUnitCodeMaps

/-!
# Comparison of the full left inverse image with the native clipped side

The comparison is over the literal original target necklace. It does not identify
an inside-bead plateau pushout with the native clipped necklace.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open CategoryTheory Limits Opposite Simplicial DaggerModels HomotopicalAlgebra
open DaggerChosenRigidificationNecklace DaggerSSetGluing
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTJointClippedSideComparison

open NecklaceCode JTTargetJointMarks JTTargetIntervalPullback
open JTTargetIntervalGluing (leftInclusion middleInclusion middlePoint middlePB middleLeft_fac)
open JTJointClippedSides (leftNative leftNative_map leftObj_fac min_over_target leftClamp_transport)
open JTNativeIntervalClamp (leftClamp leftClamp_orderMap)
open JTTargetIntervalOverMapping (overlapToLeft)
open JTJointIntervalQuotient (overlapToJoint leftQuotient leftCollapse
  jointToLeft leftCollapse_app_weak)
open DaggerOriginalProductGadget (intervalPoint_last pointMap pointIsTerminal)

noncomputable section

local instance : SmallCategory NecklaceCode := NecklaceCode.category

variable (U : NecklaceCode) (j : Joint U)

private theorem leftTargetBound (P : Over U)
    (v : Fin ((sourceInterval P.hom ⟨0, U.first_mem⟩ j
      (Fin.zero_le j.val)).len + 1)) :
    orderMap P.hom.map (orderMap (leftInclusion.{0} P.hom j) v) ≤ j.val := by
  have hf := restrict_fac P.hom ⟨0, U.first_mem⟩ j (Fin.zero_le j.val)
  have he := congrArg (fun f : (sourceInterval P.hom ⟨0, U.first_mem⟩ j
      (Fin.zero_le j.val)).toSSet ⟶ U.toSSet ↦ orderMap f v) hf
  change orderMap (restrict P.hom ⟨0, U.first_mem⟩ j (Fin.zero_le j.val) ≫
      cutLeftι U j.val) v =
    orderMap (leftInclusion.{0} P.hom j ≫ P.hom.map) v at he
  rw [orderMap_comp_apply, orderMap_comp_apply] at he
  have hi := intervalι_vertices U 0 j.val (Fin.zero_le j.val)
    (ULift.up (orderMap (restrict P.hom ⟨0, U.first_mem⟩ j
      (Fin.zero_le j.val)) v))
  have hb := (intervalEmbedding_bounds U 0 j.val (Fin.zero_le j.val)
    (orderMap (restrict P.hom ⟨0, U.first_mem⟩ j (Fin.zero_le j.val)) v)).2
  exact le_trans he.symm.le (by
    change orderMap (cutLeftι U j.val)
      (orderMap (restrict P.hom ⟨0, U.first_mem⟩ j (Fin.zero_le j.val)) v) ≤ j.val
    exact (congrArg ULift.down hi).trans_le hb)

private theorem leftTargetClamp (P : Over U) :
    (leftInclusion.{0} P.hom j ≫ leftClamp P.left (least P.hom j).val ≫
      cutLeftι P.left (least P.hom j).val) ≫ P.hom.map =
    leftInclusion.{0} P.hom j ≫ P.hom.map := by
  apply hom_ext_vertices
  funext v
  cases v with
  | up v =>
  apply ULift.ext
  calc
    orderMap ((leftInclusion.{0} P.hom j ≫ leftClamp P.left (least P.hom j).val ≫
        cutLeftι P.left (least P.hom j).val) ≫ P.hom.map) v =
      orderMap P.hom.map
        (orderMap (leftClamp P.left (least P.hom j).val ≫
          cutLeftι P.left (least P.hom j).val)
          (orderMap (leftInclusion.{0} P.hom j) v)) := by
            calc
              _ = orderMap P.hom.map
                (orderMap ((leftInclusion.{0} P.hom j ≫
                  leftClamp P.left (least P.hom j).val) ≫
                  cutLeftι P.left (least P.hom j).val) v) :=
                  orderMap_comp_apply _ P.hom.map v
              _ = _ := by
                rw [Category.assoc (leftInclusion.{0} P.hom j)
                  (leftClamp P.left (least P.hom j).val)
                  (cutLeftι P.left (least P.hom j).val), orderMap_comp_apply]
                rfl
    _ = orderMap P.hom.map
        (min (orderMap (leftInclusion.{0} P.hom j) v) (least P.hom j).val) := by
          rw [leftClamp_orderMap]
    _ = orderMap P.hom.map (orderMap (leftInclusion.{0} P.hom j) v) :=
      min_over_target U j (P := P) _ (leftTargetBound U j P v)
    _ = orderMap (leftInclusion.{0} P.hom j ≫ P.hom.map) v :=
      (orderMap_comp_apply (leftInclusion.{0} P.hom j) P.hom.map v).symm

/-- The full left inverse image maps naturally to the native clipped left side. -/
def fromFullLeft : JTTargetIntervalOverMapping.left U j ⟶
    leftNative U j ⋙ Over.post NecklaceCode.simplicialFunctor ⋙
      Over.map (cutLeftι U j.val) where
  app P := Over.homMk
    (leftInclusion.{0} P.hom j ≫ leftClamp P.left (least P.hom j).val) (by
      change (leftInclusion.{0} P.hom j ≫ leftClamp P.left (least P.hom j).val) ≫
        ((JTJointClippedSides.leftObj U j P).hom.map ≫ cutLeftι U j.val) =
        leftInclusion.{0} P.hom j ≫ P.hom.map
      rw [Category.assoc, leftObj_fac]
      exact leftTargetClamp U j P)
  naturality {P P'} g := by
    apply Over.OverMorphism.ext
    change (sourceMap P.hom ⟨0, U.first_mem⟩ j (Fin.zero_le j.val)
        g.left (Over.w g)) ≫
        (leftInclusion.{0} P'.hom j ≫ leftClamp P'.left (least P'.hom j).val) =
      (leftInclusion.{0} P.hom j ≫ leftClamp P.left (least P.hom j).val) ≫
        (((leftNative U j).map g).left.map)
    rw [leftNative_map, ← Category.assoc, sourceMap_fac]
    simp only [Category.assoc]
    rw [← Category.assoc (leftClamp P.left (least P.hom j).val)]
    rw [leftClamp_transport U j g]


private abbrev nativeLeftOver : Over U ⥤ Over U.toSSet :=
  leftNative U j ⋙ Over.post NecklaceCode.simplicialFunctor ⋙
    Over.map (cutLeftι U j.val)

/-- The joint point maps to the final vertex of the native clipped left side. -/
def jointToNativeLeft : JTJointIntervalQuotient.joint U j ⟶ nativeLeftOver U j where
  app P := Over.homMk
    (pointAt (cutLeft P.left (least P.hom j).val)
      (ULift.up (Fin.last (cutLeft P.left (least P.hom j).val).len))) (by
      change pointAt (cutLeft P.left (least P.hom j).val)
          (ULift.up (Fin.last (cutLeft P.left (least P.hom j).val).len)) ≫
        ((JTJointClippedSides.leftObj U j P).hom.map ≫ cutLeftι U j.val) =
        pointAt U (ULift.up j.val)
      rw [leftObj_fac, ← Category.assoc, pointAt_comp, cutLeftι, intervalι_vertices]
      change pointAt P.left (ULift.up (intervalEmbedding P.left 0 (least P.hom j).val
        (Fin.zero_le _) (Fin.last ((least P.hom j).val.val - 0)))) ≫ P.hom.map =
        pointAt U (ULift.up j.val)
      have he := (intervalEmbedding_last P.left 0 (least P.hom j).val (Fin.zero_le _))
      simp only [Fin.val_zero] at he
      calc
        _ = pointAt P.left (ULift.up (least P.hom j).val) ≫ P.hom.map := by
          exact congrArg (fun x ↦ pointAt P.left (ULift.up x) ≫ P.hom.map) he
        _ = pointAt U (ULift.up j.val) := by
          rw [pointAt_comp]
          apply congrArg (pointAt U)
          apply ULift.ext
          exact (least P.hom j).property)
  naturality {P P'} g := by
    apply Over.OverMorphism.ext
    dsimp [JTJointIntervalQuotient.joint, nativeLeftOver]
    rw [Category.id_comp]
    change pointAt (cutLeft P'.left (least P'.hom j).val)
        (ULift.up (Fin.last (cutLeft P'.left (least P'.hom j).val).len)) =
      pointAt (cutLeft P.left (least P.hom j).val)
        (ULift.up (Fin.last (cutLeft P.left (least P.hom j).val).len)) ≫
      ((leftNative U j).map g).left.map
    rw [pointAt_comp]
    apply congrArg (pointAt (cutLeft P'.left (least P'.hom j).val))
    apply ULift.ext
    exact (orderMap_last (((leftNative U j).map g).left)).symm


private theorem throughPoint {A T : NecklaceCode} (m : A.toSSet ⟶ Δ[0])
    (v : Fin (T.len + 1)) (a : Fin (A.len + 1)) :
    orderMap (m ≫ pointAt T (ULift.up v)) a = v := by
  change (T.verticesEquiv ((pointAt T (ULift.up v)).app _
    (m.app _ (A.verticesEquiv.symm (ULift.up a))))).down = _
  rw [pointAt, pointAt_vertex_apply, Equiv.apply_symm_apply]

/-- The full overlap maps to the final point of the native clipped left side. -/
theorem overlap_eq : overlapToLeft U j ≫ fromFullLeft U j =
    overlapToJoint U j ≫ jointToNativeLeft U j := by
  apply NatTrans.ext
  funext P
  apply Over.OverMorphism.ext
  let c := (least P.hom j).val
  let i := cutLeftι P.left c
  let r := leftClamp P.left c
  have : Mono i := inferInstanceAs (Mono (intervalι P.left 0 c (Fin.zero_le _)))
  apply (cancel_mono i).mp
  change (JTTargetIntervalGluing.middleLeft P.hom j ≫
      (leftInclusion.{0} P.hom j ≫ r)) ≫ i =
    (middlePoint P.hom j ≫
      pointAt (cutLeft P.left c) (ULift.up (Fin.last (cutLeft P.left c).len))) ≫ i
  rw [← Category.assoc (JTTargetIntervalGluing.middleLeft P.hom j),
    middleLeft_fac, Category.assoc, Category.assoc]
  have h : pointAt (cutLeft P.left c) (ULift.up (Fin.last (cutLeft P.left c).len)) ≫
      i = pointAt P.left (ULift.up c) :=
    intervalPoint_last P.left 0 c (Fin.zero_le _)
  rw [h]
  apply hom_ext_vertices
  funext v
  cases v with
  | up v =>
  apply ULift.ext
  have hv : orderMap P.hom.map (orderMap (middleInclusion P.hom j) v) = j.val :=
    (orderMap_comp_apply (middleInclusion P.hom j) P.hom.map v).symm.trans
      ((congrArg (fun f ↦ orderMap f v) (middlePB P.hom j).w).trans (throughPoint _ _ _))
  have hb : c ≤ orderMap (middleInclusion P.hom j) v :=
    (least_le_iff P.hom j _).2 hv.ge
  exact (orderMap_comp_apply (middleInclusion P.hom j) (r ≫ i) v).trans
    ((leftClamp_orderMap _ _ _).trans
      ((min_eq_right hb).trans (throughPoint _ _ _).symm))

/-- The actual left pushout quotient maps to the native clipped left side. -/
def fromLeftQuotient : leftQuotient U j ⟶ nativeLeftOver U j :=
  pushout.desc (fromFullLeft U j) (jointToNativeLeft U j) (overlap_eq U j)

@[reassoc]
theorem leftCollapse_fromLeftQuotient :
    leftCollapse U j ≫ fromLeftQuotient U j = fromFullLeft U j :=
  pushout.inl_desc _ _ _

@[reassoc]
theorem jointToLeft_fromLeftQuotient :
    jointToLeft U j ≫ fromLeftQuotient U j = jointToNativeLeft U j :=
  pushout.inr_desc _ _ _

/-- The actual left quotient is Kan weakly equivalent to the clipped comparison. -/
theorem fromLeftQuotient_app_weak (P : Over U) :
    WeakEquivalence ((fromLeftQuotient U j).app P).left := by
  let A := (sourceInterval P.hom ⟨0, U.first_mem⟩ j (Fin.zero_le _)).toSSet
  let B := (cutLeft P.left (least P.hom j).val).toSSet
  have : WeakEquivalence (pointMap A) :=
    (weakEquivalence_iff_GW _).mpr (JTNativeTargetKanWeak.point_GW _)
  have : WeakEquivalence (pointMap B) :=
    (weakEquivalence_iff_GW _).mpr (JTNativeTargetKanWeak.point_GW _)
  have : WeakEquivalence ((fromFullLeft U j).app P).left :=
    weakEquivalence_of_postcomp_of_fac
      (pointIsTerminal.hom_ext (((fromFullLeft U j).app P).left ≫ pointMap B) (pointMap A))
  have := leftCollapse_app_weak U j P
  exact weakEquivalence_of_precomp_of_fac
    (congrArg (fun w : JTTargetIntervalOverMapping.left U j ⟶ nativeLeftOver U j ↦
      (w.app P).left) (leftCollapse_fromLeftQuotient U j))

end

end DaggerModels.PartII.JTJointClippedSideComparison
