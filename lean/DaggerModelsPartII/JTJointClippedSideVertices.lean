import DaggerModelsPartII.JTJointClippedSideComparison
import DaggerModelsPartII.JTJointClippedRightVertices

/-! Degree-zero comparison for the left native interval quotient. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTJointClippedSideVertices

open NecklaceCode JTTargetJointMarks JTTargetIntervalPullback
open JTJointClippedSideComparison (fromFullLeft fromLeftQuotient jointToNativeLeft
  leftCollapse_fromLeftQuotient jointToLeft_fromLeftQuotient)
open JTNativeIntervalClamp (leftClamp leftClamp_orderMap)
open JTJointClippedRightVertices (type_isPushout_of_clamp
  type_bijective_of_pushout_comparison)
open JTTargetIntervalGluing (leftInclusion middleInclusion middleLeft middleLeft_fac)

noncomputable section

local instance : SmallCategory NecklaceCode := NecklaceCode.category

variable (U : NecklaceCode) (j : Joint U) (P : Over U)

private abbrev firstJoint : Joint U := ⟨0, U.first_mem⟩
private abbrev p := (least P.hom j).val
private abbrev q := (greatest P.hom j).val
private abbrev a := (least P.hom (firstJoint U)).val
private abbrev full := sourceInterval P.hom (firstJoint U) j (Fin.zero_le j.val)
private abbrev common := sourceInterval P.hom j j le_rfl

private theorem a_zero : a U P = 0 := by
  apply le_antisymm _ (Fin.zero_le _)
  apply (least_le_iff P.hom (firstJoint U) 0).2
  change (0 : Fin (U.len + 1)) ≤ orderMap P.hom.map 0
  exact (orderMap_first P.hom).symm.le

private theorem p_le_q : p U j P ≤ q U j P :=
  le_greatest (least P.hom) j

private theorem a_le_q : a U P ≤ q U j P := by
  rw [a_zero]
  exact Fin.zero_le _

private theorem shortBounds
    (x : (cutLeft P.left (p U j P)).toSSet.obj (op ⦋0⦌)) :
    a U P ≤ P.left.inclusion.app _ ((cutLeftι P.left (p U j P)).app _ x) 0 ∧
      P.left.inclusion.app _ ((cutLeftι P.left (p U j P)).app _ x) 0 ≤ q U j P := by
  rw [a_zero]
  change (0 : Fin (P.left.len + 1)) ≤ _ ∧ _ ≤ q U j P
  have h := (intervalEmbedding_bounds P.left 0 (p U j P) (Fin.zero_le _)
    ((cutLeft P.left (p U j P)).inclusion.app _ x 0)).2
  simp only [cutLeftι, intervalι_apply]
  exact ⟨Fin.zero_le _, h.trans (p_le_q U j P)⟩

/-- Inclusion of the short native side into the full left inverse image. -/
def shortToFull : (cutLeft P.left (p U j P)).toSSet ⟶ (full U j P).toSSet :=
  intervalFactor P.left (a U P) (q U j P) (a_le_q U j P)
    (cutLeftι P.left (p U j P)) (shortBounds U j P)

@[reassoc]
theorem shortToFull_fac :
    shortToFull U j P ≫ leftInclusion P.hom j = cutLeftι P.left (p U j P) :=
  intervalFactor_fac P.left (a U P) (q U j P) (a_le_q U j P)
    (cutLeftι P.left (p U j P)) (shortBounds U j P)


/-- The short native side is a retract of the full left inverse image under clipping. -/
theorem shortToFull_clamp :
    shortToFull U j P ≫ leftInclusion P.hom j ≫ leftClamp P.left (p U j P) = 𝟙 _ := by
  have : Mono (cutLeftι.{0} P.left (p U j P)) :=
    inferInstanceAs (Mono (intervalι P.left 0 (p U j P) (Fin.zero_le _)))
  apply (cancel_mono (cutLeftι P.left (p U j P))).mp
  rw [Category.id_comp, ← Category.assoc (shortToFull U j P)
    (leftInclusion P.hom j) (leftClamp P.left (p U j P)), shortToFull_fac]
  apply hom_ext_vertices
  funext v
  cases v with
  | up v =>
  apply ULift.ext
  have hi : orderMap (cutLeftι P.left (p U j P)) v =
      intervalEmbedding P.left 0 (p U j P) (Fin.zero_le _) v :=
    congrArg ULift.down
      (intervalι_vertices P.left 0 (p U j P) (Fin.zero_le _) (ULift.up v))
  have hb := (intervalEmbedding_bounds P.left 0 (p U j P) (Fin.zero_le _) v).2
  calc
    _ = orderMap (leftClamp P.left (p U j P) ≫ cutLeftι P.left (p U j P))
        (orderMap (cutLeftι P.left (p U j P)) v) :=
      orderMap_comp_apply _ _ v
    _ = min (orderMap (cutLeftι P.left (p U j P)) v) (p U j P) :=
      leftClamp_orderMap _ _ _
    _ = orderMap (cutLeftι P.left (p U j P)) v := min_eq_left (hi.trans_le hb)

private theorem fullClamp_surjective :
    Function.Surjective (((fromFullLeft U j).app P).left.app (op ⦋0⦌)) := by
  intro y
  let x := (shortToFull U j P).app (op ⦋0⦌) y
  refine ⟨x, ?_⟩
  have h := congrFun (NatTrans.congr_app (shortToFull_clamp U j P) (op ⦋0⦌)) y
  exact h


private theorem fullOrder (v : Fin ((full U j P).len + 1)) :
    orderMap (leftInclusion.{0} P.hom j) v =
      intervalEmbedding P.left (a U P) (q U j P) (a_le_q U j P) v :=
  congrArg ULift.down
    (intervalι_vertices P.left (a U P) (q U j P) (a_le_q U j P) (ULift.up v))

private theorem commonOrder (v : Fin ((common U j P).len + 1)) :
    orderMap (middleInclusion.{0} P.hom j) v =
      intervalEmbedding P.left (p U j P) (q U j P) (p_le_q U j P) v :=
  congrArg ULift.down
    (intervalι_vertices P.left (p U j P) (q U j P) (p_le_q U j P) (ULift.up v))

private theorem fullBound (v : Fin ((full U j P).len + 1)) :
    a U P ≤ orderMap (leftInclusion.{0} P.hom j) v ∧
      orderMap (leftInclusion.{0} P.hom j) v ≤ q U j P := by
  rw [fullOrder]
  exact intervalEmbedding_bounds P.left (a U P) (q U j P) (a_le_q U j P) v

private theorem commonInFull (x : (full U j P).toSSet.obj (op ⦋0⦌))
    (hx : p U j P ≤ orderMap (leftInclusion.{0} P.hom j)
      ((full U j P).verticesEquiv x).down) :
    x ∈ Set.range ((middleLeft P.hom j).app (op ⦋0⦌)) := by
  let v := ((full U j P).verticesEquiv x).down
  let z := orderMap (leftInclusion.{0} P.hom j) v
  have hz : z ≤ q U j P := (fullBound U j P v).2
  obtain ⟨w, hw⟩ := intervalEmbedding_preimage P.left
    (p U j P) (q U j P) (p_le_q U j P) z hx hz
  let y := (common U j P).verticesEquiv.symm (ULift.up w)
  have he : (middleInclusion.{0} P.hom j).app (op ⦋0⦌) y =
      (leftInclusion.{0} P.hom j).app (op ⦋0⦌) x := by
    apply P.left.verticesEquiv.injective
    apply ULift.ext
    have hy : (P.left.verticesEquiv ((middleInclusion.{0} P.hom j).app _ y)).down =
        orderMap (middleInclusion.{0} P.hom j) w := by
      dsimp [orderMap, mapVertices, y]
      rfl
    have hx' : (P.left.verticesEquiv ((leftInclusion.{0} P.hom j).app _ x)).down =
        orderMap (leftInclusion.{0} P.hom j) v := by
      have e : (full U j P).verticesEquiv.symm (ULift.up v) = x := by
        have e' : (ULift.up v : Vertices.{0} (full U j P)) =
            (full U j P).verticesEquiv x := by
          change ULift.up ((full U j P).verticesEquiv x).down =
            (full U j P).verticesEquiv x
          cases (full U j P).verticesEquiv x
          rfl
        rw [e', Equiv.symm_apply_apply]
      change (P.left.verticesEquiv ((leftInclusion.{0} P.hom j).app _ x)).down =
        (P.left.verticesEquiv ((leftInclusion.{0} P.hom j).app _
          ((full U j P).verticesEquiv.symm (ULift.up v)))).down
      rw [e]
    rw [hy, hx', commonOrder, hw]
  refine ⟨y, ?_⟩
  have hf := congrFun (NatTrans.congr_app (middleLeft_fac P.hom j) (op ⦋0⦌)) y
  change (leftInclusion.{0} P.hom j).app _ ((middleLeft P.hom j).app _ y) =
    (middleInclusion.{0} P.hom j).app _ y at hf
  apply intervalι_injective_app P.left (a U P) (q U j P) (a_le_q U j P) _
  exact hf.trans he


private theorem vertexOrder {A B : NecklaceCode} (f : toSSet.{0} A ⟶ toSSet.{0} B)
    (x : (toSSet.{0} A).obj (op ⦋0⦌)) :
    orderMap f (A.verticesEquiv x).down = (B.verticesEquiv (f.app _ x)).down := by
  dsimp [orderMap, mapVertices]
  have e : (ULift.up (A.verticesEquiv x).down : Vertices.{0} A) = A.verticesEquiv x := by
    cases A.verticesEquiv x
    rfl
  rw [e, Equiv.symm_apply_apply]

private theorem fullClampOrder (v : Fin ((full U j P).len + 1)) :
    orderMap (leftInclusion.{0} P.hom j ≫ leftClamp P.left (p U j P) ≫
      cutLeftι P.left (p U j P)) v =
    min (orderMap (leftInclusion.{0} P.hom j) v) (p U j P) := by
  exact (orderMap_comp_apply (leftInclusion.{0} P.hom j)
    (leftClamp P.left (p U j P) ≫ cutLeftι P.left (p U j P)) v).trans
    (leftClamp_orderMap _ _ _)

private theorem pointVertex (x : (Δ[0] : SSet.{0}).obj (op ⦋0⦌)) :
    ((cutLeft P.left (p U j P)).verticesEquiv
      ((pointAt (cutLeft P.left (p U j P))
        (ULift.up (Fin.last (cutLeft P.left (p U j P)).len))).app _ x)).down =
      Fin.last (cutLeft P.left (p U j P)).len := by
  rw [pointAt, pointAt_vertex_apply, Equiv.apply_symm_apply]


private theorem targetJointOfEq (x : (full U j P).toSSet.obj (op ⦋0⦌))
    (y : (Δ[0] : SSet.{0}).obj (op ⦋0⦌))
    (h : ((fromFullLeft U j).app P).left.app (op ⦋0⦌) x =
      ((jointToNativeLeft U j).app P).left.app (op ⦋0⦌) y) :
    orderMap P.hom.map (orderMap (leftInclusion.{0} P.hom j)
      ((full U j P).verticesEquiv x).down) = j.val := by
  have hl := congrFun
    (NatTrans.congr_app (Over.w ((fromFullLeft U j).app P)) (op ⦋0⦌)) x
  have hr := congrFun
    (NatTrans.congr_app (Over.w ((jointToNativeLeft U j).app P)) (op ⦋0⦌)) y
  have ht : (leftInclusion.{0} P.hom j ≫ P.hom.map).app _ x =
      (pointAt U (ULift.up j.val)).app _ y := by
    exact hl.symm.trans ((congrArg
      (fun z ↦ ((JTJointClippedSides.leftObj U j P).hom.map ≫ cutLeftι U j.val).app _ z)
      h).trans hr)
  have hv := congrArg (fun z ↦ (U.verticesEquiv z).down) ht
  change (U.verticesEquiv ((leftInclusion.{0} P.hom j ≫ P.hom.map).app _ x)).down =
    (U.verticesEquiv ((pointAt U (ULift.up j.val)).app _ y)).down at hv
  have he := vertexOrder (leftInclusion.{0} P.hom j ≫ P.hom.map) x
  have ht' := he.trans hv
  rw [orderMap_comp_apply] at ht'
  simpa only [pointAt, pointAt_vertex_apply, Equiv.apply_symm_apply] using ht' 

private theorem fullFiber (x : (full U j P).toSSet.obj (op ⦋0⦌))
    (y : (Δ[0] : SSet.{0}).obj (op ⦋0⦌))
    (h : ((fromFullLeft U j).app P).left.app (op ⦋0⦌) x =
      ((jointToNativeLeft U j).app P).left.app (op ⦋0⦌) y) :
    ∃ z : (common U j P).toSSet.obj (op ⦋0⦌),
      (middleLeft P.hom j).app _ z = x ∧
        (JTTargetIntervalGluing.middlePoint P.hom j).app _ z = y := by
  obtain ⟨z, hz⟩ := commonInFull U j P x
    ((least_le_iff P.hom j _).2 (targetJointOfEq U j P x y h).ge)
  refine ⟨z, hz, ?_⟩
  exact zeroSimplex_unique _ |>.trans (zeroSimplex_unique y).symm


private theorem outside_lt (x : (full U j P).toSSet.obj (op ⦋0⦌))
    (hx : x ∉ Set.range ((middleLeft P.hom j).app (op ⦋0⦌))) :
    orderMap (leftInclusion.{0} P.hom j) ((full U j P).verticesEquiv x).down <
      p U j P := by
  apply lt_of_not_ge
  intro h
  exact hx (commonInFull U j P x h)

private theorem fullClamp_injective_off
    (x y : (full U j P).toSSet.obj (op ⦋0⦌))
    (hx : x ∉ Set.range ((middleLeft P.hom j).app (op ⦋0⦌)))
    (hy : y ∉ Set.range ((middleLeft P.hom j).app (op ⦋0⦌)))
    (h : ((fromFullLeft U j).app P).left.app (op ⦋0⦌) x =
      ((fromFullLeft U j).app P).left.app (op ⦋0⦌) y) : x = y := by
  let vx := ((full U j P).verticesEquiv x).down
  let vy := ((full U j P).verticesEquiv y).down
  let cx := orderMap (leftInclusion.{0} P.hom j) vx
  let cy := orderMap (leftInclusion.{0} P.hom j) vy
  have hcx : cx ≤ p U j P := (outside_lt U j P x hx).le
  have hcy : cy ≤ p U j P := (outside_lt U j P y hy).le
  have he : orderMap (leftInclusion.{0} P.hom j ≫ leftClamp P.left (p U j P) ≫
      cutLeftι P.left (p U j P)) vx =
      orderMap (leftInclusion.{0} P.hom j ≫ leftClamp P.left (p U j P) ≫
      cutLeftι P.left (p U j P)) vy := by
    have ex := vertexOrder
      (leftInclusion.{0} P.hom j ≫ leftClamp P.left (p U j P) ≫
        cutLeftι P.left (p U j P)) x
    have ey := vertexOrder
      (leftInclusion.{0} P.hom j ≫ leftClamp P.left (p U j P) ≫
        cutLeftι P.left (p U j P)) y
    exact ex.trans ((congrArg
      (fun z ↦ (P.left.verticesEquiv ((cutLeftι P.left (p U j P)).app _ z)).down)
      h).trans ey.symm)
  rw [fullClampOrder U j P vx, fullClampOrder U j P vy,
    min_eq_left hcx, min_eq_left hcy] at he
  have hmap : (leftInclusion.{0} P.hom j).app (op ⦋0⦌) x =
      (leftInclusion.{0} P.hom j).app (op ⦋0⦌) y := by
    apply P.left.verticesEquiv.injective
    apply ULift.ext
    exact (vertexOrder (leftInclusion.{0} P.hom j) x).symm.trans
      (he.trans (vertexOrder (leftInclusion.{0} P.hom j) y))
  exact intervalι_injective_app P.left (a U P) (q U j P) (a_le_q U j P) _ hmap


private theorem middleLeft_injective :
    Function.Injective ((middleLeft P.hom j).app (op ⦋0⦌)) := by
  intro x y h
  have hx := congrFun (NatTrans.congr_app (middleLeft_fac P.hom j) (op ⦋0⦌)) x
  have hy := congrFun (NatTrans.congr_app (middleLeft_fac P.hom j) (op ⦋0⦌)) y
  have he : (middleInclusion.{0} P.hom j).app _ x =
      (middleInclusion.{0} P.hom j).app _ y := by
    exact hx.symm.trans ((congrArg ((leftInclusion.{0} P.hom j).app _) h).trans hy)
  exact intervalι_injective_app P.left (p U j P) (q U j P) (p_le_q U j P) _ he

private theorem jointPoint_injective : Function.Injective
    (((jointToNativeLeft U j).app P).left.app (op ⦋0⦌)) := by
  intro x y _
  exact (zeroSimplex_unique x).trans (zeroSimplex_unique y).symm

private theorem clippedVertices_isPushout : IsPushout
    (((JTTargetIntervalOverMapping.overlapToLeft U j).app P).left.app (op ⦋0⦌))
    (((JTJointIntervalQuotient.overlapToJoint U j).app P).left.app (op ⦋0⦌))
    (((fromFullLeft U j).app P).left.app (op ⦋0⦌))
    (((jointToNativeLeft U j).app P).left.app (op ⦋0⦌)) := by
  apply type_isPushout_of_clamp
  · exact middleLeft_injective U j P
  · exact jointPoint_injective U j P
  · exact congrArg (fun t : JTTargetIntervalOverMapping.overlap U j ⟶
        (JTJointClippedSides.leftNative U j ⋙
          Over.post NecklaceCode.simplicialFunctor ⋙ Over.map (cutLeftι U j.val)) ↦
        (((t.app P).left).app (op ⦋0⦌)))
      (JTJointClippedSideComparison.overlap_eq U j)
  · exact fullClamp_surjective U j P
  · intro x y h
    exact fullFiber U j P x y h
  · intro x y hx hy h
    exact fullClamp_injective_off U j P x y hx hy h


private theorem quotientVertices_isPushout : IsPushout
    (((JTTargetIntervalOverMapping.overlapToLeft U j).app P).left.app (op ⦋0⦌))
    (((JTJointIntervalQuotient.overlapToJoint U j).app P).left.app (op ⦋0⦌))
    (((JTJointIntervalQuotient.leftCollapse U j).app P).left.app (op ⦋0⦌))
    (((JTJointIntervalQuotient.jointToLeft U j).app P).left.app (op ⦋0⦌)) := by
  let E := (evaluation (Over U) (Over U.toSSet)).obj P ⋙ Over.forget U.toSSet
  have hs := (IsPushout.of_hasPushout
    (JTTargetIntervalOverMapping.overlapToLeft U j)
    (JTJointIntervalQuotient.overlapToJoint U j)).map E
  have ht := hs.map (SSet.evaluation.obj (op ⦋0⦌))
  exact ht

/-- The actual left quotient and native clipped left side have the same vertices. -/
theorem fromLeftQuotient_vertices_bijective : Function.Bijective
    (((fromLeftQuotient U j).app P).left.app (op ⦋0⦌)) := by
  apply type_bijective_of_pushout_comparison
    (quotientVertices_isPushout U j P) (clippedVertices_isPushout U j P)
  · exact congrArg (fun t ↦ (((t.app P).left).app (op ⦋0⦌)))
      (leftCollapse_fromLeftQuotient U j)
  · exact congrArg (fun t ↦ (((t.app P).left).app (op ⦋0⦌)))
      (jointToLeft_fromLeftQuotient U j)

end

end DaggerModels.PartII.JTJointClippedSideVertices
