import DaggerModelsPartII.JTJointClippedSides
import DaggerModelsPartII.JTJointIntervalQuotient
import ChosenNecklaceUnitCodeMaps

/-! Compare the full right interval with its clipped necklace over the original target. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerChosenRigidificationNecklace DaggerSSetGluing
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTJointClippedRightComparison

open NecklaceCode JTTargetJointMarks JTTargetIntervalPullback
open JTTargetIntervalOverMapping (right overlap overlapToRight)
open JTTargetIntervalGluing (rightInclusion middleInclusion middlePoint middlePB middleRight_fac)
open JTNativeIntervalClamp (rightClamp rightClamp_orderMap)
open JTJointClippedSides (rightNative rightNative_map rightObj_fac rightClamp_transport
  max_over_target)
open JTJointIntervalQuotient (joint overlapToJoint rightQuotient rightCollapse jointToRight
  rightCollapse_app_weak)
open DaggerOriginalProductGadget (intervalPoint_first pointMap pointIsTerminal)

noncomputable section

variable (U : NecklaceCode) (j : Joint U)

private abbrev endJoint : Joint U := ⟨Fin.last U.len, U.last_mem⟩
private abbrev code (P : Over U) := sourceInterval P.hom j (endJoint U) (Fin.le_last _)
private abbrev p (P : Over U) := (greatest P.hom j).val

/-- The clipped right side, regarded over the entire original target. -/
def clipped : Over U ⥤ Over U.toSSet :=
  rightNative U j ⋙ Over.post NecklaceCode.simplicialFunctor ⋙ Over.map (cutRightι U j.val)

private theorem vertex_bound (P : Over U) (v : Fin ((code U j P).len + 1)) :
    j.val ≤ orderMap P.hom.map (orderMap (rightInclusion.{0} P.hom j) v) := by
  let ι := rightInclusion.{0} P.hom j
  let r := restrict P.hom j (endJoint U) (Fin.le_last _)
  have e : r ≫ cutRightι U j.val = ι ≫ P.hom.map := restrict_fac _ _ _ _
  have h : orderMap (cutRightι U j.val) (orderMap r v) =
      intervalEmbedding U j.val (Fin.last U.len) (Fin.le_last _) (orderMap r v) :=
    congrArg ULift.down (intervalι_vertices U j.val (Fin.last U.len) (Fin.le_last _)
      (ULift.up (orderMap r v)))
  have e' : orderMap P.hom.map (orderMap (rightInclusion.{0} P.hom j) v) =
      intervalEmbedding U j.val (Fin.last U.len) (Fin.le_last _) (orderMap r v) := by
    calc
      _ = orderMap (ι ≫ P.hom.map) v := (orderMap_comp_apply ι P.hom.map v).symm
      _ = orderMap (r ≫ cutRightι U j.val) v := congrArg (fun f ↦ orderMap f v) e.symm
      _ = orderMap (cutRightι U j.val) (orderMap r v) := orderMap_comp_apply r _ v
      _ = _ := h
  exact (intervalEmbedding_bounds U j.val (Fin.last U.len) (Fin.le_last _) _).1.trans_eq
    e'.symm


private theorem by_orderMap {T T' : NecklaceCode} {f g : T.toSSet ⟶ T'.toSSet}
    (h : ∀ v, orderMap f v = orderMap g v) : f = g := by
  apply hom_ext_vertices
  funext v
  cases v with
  | up v => exact ULift.ext _ _ (h v)

private theorem right_clamp_over (P : Over U) :
    (rightInclusion.{0} P.hom j ≫
        (rightClamp P.left (p U j P) ≫ cutRightι P.left (p U j P))) ≫ P.hom.map =
      rightInclusion.{0} P.hom j ≫ P.hom.map := by
  let i := rightInclusion.{0} P.hom j
  let c := rightClamp P.left (p U j P) ≫ cutRightι P.left (p U j P)
  apply by_orderMap (T := code U j P) (T' := U)
  intro v
  calc
    _ = orderMap P.hom.map (orderMap (i ≫ c) v) := orderMap_comp_apply (i ≫ c) P.hom.map v
    _ = orderMap P.hom.map (max (orderMap i v) (p U j P)) :=
      congrArg (fun a ↦ orderMap P.hom.map a)
        ((orderMap_comp_apply i c v).trans (rightClamp_orderMap _ _ _))
    _ = orderMap P.hom.map (orderMap i v) :=
      max_over_target U j _ (vertex_bound U j P v)
    _ = _ := (orderMap_comp_apply i P.hom.map v).symm

/-- The full original right interval maps naturally to the clipped right side over the target. -/
def fromFull : right U j ⟶ clipped U j where
  app P := Over.homMk (rightInclusion.{0} P.hom j ≫ rightClamp P.left (p U j P)) (by
    change (rightInclusion.{0} P.hom j ≫ rightClamp P.left (p U j P)) ≫
        ((JTJointClippedSides.rightObj U j P).hom.map ≫ cutRightι U j.val) =
      rightInclusion.{0} P.hom j ≫ P.hom.map
    rw [rightObj_fac]
    simpa only [Category.assoc] using right_clamp_over U j P)
  naturality P P' g := by
    apply Over.OverMorphism.ext
    change sourceMap P.hom j (endJoint U) (Fin.le_last _) g.left (Over.w g) ≫
        (rightInclusion.{0} P'.hom j ≫ rightClamp P'.left (p U j P')) =
      (rightInclusion.{0} P.hom j ≫ rightClamp P.left (p U j P)) ≫
        ((rightNative U j).map g).left.map
    have hf : sourceMap P.hom j (endJoint U) (Fin.le_last _) g.left (Over.w g) ≫
        rightInclusion.{0} P'.hom j = rightInclusion.{0} P.hom j ≫ g.left.map :=
      sourceMap_fac P.hom j (endJoint U) (Fin.le_last _) g.left (Over.w g)
    rw [← Category.assoc, hf, rightNative_map]
    symm
    simpa only [Category.assoc] using congrArg (rightInclusion.{0} P.hom j ≫ ·)
      (rightClamp_transport U j g)


/-- Both right constructions use the same actual point at the joint. -/
def fromJoint : joint U j ⟶ clipped U j where
  app P := Over.homMk (pointAt (cutRight P.left (p U j P)) (ULift.up 0)) (by
    change pointAt (cutRight P.left (p U j P)) (ULift.up 0) ≫
        ((JTJointClippedSides.rightObj U j P).hom.map ≫ cutRightι U j.val) =
      pointAt U (ULift.up j.val)
    rw [rightObj_fac, ← Category.assoc]
    change (pointAt (cutRight P.left (p U j P)) (ULift.up 0) ≫
      cutRightι P.left (p U j P)) ≫ P.hom.map = pointAt U (ULift.up j.val)
    have h : pointAt (cutRight P.left (p U j P)) (ULift.up 0) ≫
        cutRightι P.left (p U j P) = pointAt P.left (ULift.up (p U j P)) :=
      intervalPoint_first P.left (p U j P) (Fin.last P.left.len) (Fin.le_last _)
    rw [h, pointAt_comp]
    exact congrArg (pointAt U) (ULift.ext _ _ (greatest P.hom j).property))
  naturality P P' g := by
    apply Over.OverMorphism.ext
    change (𝟙 (Δ[0] : SSet.{0})) ≫ pointAt (cutRight P'.left (p U j P')) (ULift.up 0) =
      pointAt (cutRight P.left (p U j P)) (ULift.up 0) ≫ ((rightNative U j).map g).left.map
    rw [Category.id_comp]
    exact (pointAt_first_comp ((rightNative U j).map g).left).symm

private theorem through_point {A T : NecklaceCode} (m : A.toSSet ⟶ Δ[0])
    (v : Fin (T.len + 1)) (a : Fin (A.len + 1)) :
    orderMap (m ≫ pointAt T (ULift.up v)) a = v := by
  change (T.verticesEquiv ((pointAt T (ULift.up v)).app _
    (m.app _ (A.verticesEquiv.symm (ULift.up a))))).down = _
  rw [pointAt, pointAt_vertex_apply, Equiv.apply_symm_apply]

/-- The full overlap maps to the actual first point of the clipped right necklace. -/
theorem overlap_eq :
    overlapToRight U j ≫ fromFull U j = overlapToJoint U j ≫ fromJoint U j := by
  apply NatTrans.ext
  funext P
  apply Over.OverMorphism.ext
  let c := p U j P
  let ι := cutRightι P.left c
  let r := rightClamp P.left c
  haveI : Mono ι := inferInstanceAs
    (Mono (intervalι P.left c (Fin.last P.left.len) (Fin.le_last _)))
  apply (cancel_mono ι).mp
  change (JTTargetIntervalGluing.middleRight P.hom j ≫
      (rightInclusion.{0} P.hom j ≫ r)) ≫ ι =
    (middlePoint P.hom j ≫ pointAt (cutRight P.left c) (ULift.up 0)) ≫ ι
  rw [← Category.assoc (JTTargetIntervalGluing.middleRight P.hom j), middleRight_fac,
    Category.assoc, Category.assoc]
  have h : pointAt (cutRight P.left c) (ULift.up 0) ≫ ι = pointAt P.left (ULift.up c) :=
    intervalPoint_first P.left c (Fin.last P.left.len) (Fin.le_last _)
  rw [h]
  apply by_orderMap (T := sourceInterval P.hom j j le_rfl) (T' := P.left)
  intro v
  have hv : orderMap P.hom.map (orderMap (middleInclusion P.hom j) v) = j.val :=
    (orderMap_comp_apply (middleInclusion P.hom j) P.hom.map v).symm.trans
      ((congrArg (fun f ↦ orderMap f v) (middlePB P.hom j).w).trans (through_point _ _ _))
  have hb : orderMap (middleInclusion P.hom j) v ≤ c :=
    (le_greatest_iff P.hom j _).2 hv.le
  exact (orderMap_comp_apply (middleInclusion P.hom j) (r ≫ ι) v).trans
    ((rightClamp_orderMap _ _ _).trans
      ((max_eq_right hb).trans (through_point _ _ _).symm))

/-- The actual right pushout quotient maps to the clipped right side over the fixed target. -/
def fromQuotient : rightQuotient U j ⟶ clipped U j :=
  pushout.desc (fromFull U j) (fromJoint U j) (overlap_eq U j)

@[reassoc]
theorem collapse_fromQuotient : rightCollapse U j ≫ fromQuotient U j = fromFull U j :=
  pushout.inl_desc _ _ _

@[reassoc]
theorem joint_fromQuotient : jointToRight U j ≫ fromQuotient U j = fromJoint U j :=
  pushout.inr_desc _ _ _

/-- The actual right quotient is Kan weakly equivalent to its native clipped comparison. -/
theorem fromQuotient_app_weak (P : Over U) : WeakEquivalence ((fromQuotient U j).app P).left := by
  let A := (code U j P).toSSet
  let B := (cutRight P.left (p U j P)).toSSet
  haveI : WeakEquivalence (pointMap A) :=
    (weakEquivalence_iff_GW _).mpr (JTNativeTargetKanWeak.point_GW _)
  haveI : WeakEquivalence (pointMap B) :=
    (weakEquivalence_iff_GW _).mpr (JTNativeTargetKanWeak.point_GW _)
  haveI : WeakEquivalence ((fromFull U j).app P).left :=
    weakEquivalence_of_postcomp_of_fac
      (pointIsTerminal.hom_ext (((fromFull U j).app P).left ≫ pointMap B) (pointMap A))
  haveI := rightCollapse_app_weak U j P
  exact weakEquivalence_of_precomp_of_fac
    (congrArg (fun w : right U j ⟶ clipped U j ↦ (w.app P).left) (collapse_fromQuotient U j))

end
end DaggerModels.PartII.JTJointClippedRightComparison
