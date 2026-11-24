import DaggerModelsPartII.JTJointClippedRightComparison
import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-! Degree-zero comparison for the clipped right interval. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTJointClippedRightVertices

open NecklaceCode JTTargetJointMarks JTTargetIntervalPullback
open JTTargetIntervalOverMapping (right overlap overlapToRight)
open JTTargetIntervalGluing (rightInclusion middleInclusion middlePoint middleRight_fac)
open JTNativeIntervalClamp (rightClamp rightClamp_orderMap)
open JTJointClippedRightComparison (clipped fromFull fromJoint fromQuotient
  overlap_eq collapse_fromQuotient joint_fromQuotient)
open JTJointIntervalQuotient (joint overlapToJoint rightQuotient rightCollapse jointToRight)

noncomputable section

/-- A surjective clamp whose only nontrivial fibers lie in an included overlap
    forms a pushout after the overlap is collapsed to an embedded point. -/
theorem type_isPushout_of_clamp {A B C D : Type}
    (f : A ⟶ B) (g : A ⟶ C) (r : B ⟶ D) (s : C ⟶ D)
    (hf : Function.Injective f) (hs : Function.Injective s)
    (w : f ≫ r = g ≫ s) (hr : Function.Surjective r)
    (hfiber : ∀ b c, r b = s c → ∃ a, f a = b ∧ g a = c)
    (hker : ∀ x y, x ∉ Set.range f → y ∉ Set.range f → r x = r y → x = y) :
    IsPushout f g r s := by
  haveI : Mono s := (mono_iff_injective s).mpr hs
  have hpb : IsPullback g f s r := by
    apply (CategoryTheory.Limits.Types.isPullback_iff g s f r).mpr
    refine ⟨w.symm, ?_, ?_⟩
    · intro x y h
      exact hf h.2
    · intro c b h
      obtain ⟨a, ha, hb⟩ := hfiber b c h.symm
      exact ⟨a, hb, ha⟩
  have hcover : Set.range s ⊔ Set.range r = Set.univ := by
    ext d
    simp only [Set.sup_eq_union, Set.mem_union, Set.mem_univ, iff_true]
    exact Or.inr (hr d)
  exact (CategoryTheory.Limits.Types.isPushout_of_isPullback_of_mono'
    hpb hcover hker).flip

/-- The map between two pushout vertices that preserves both legs is bijective. -/
theorem type_bijective_of_pushout_comparison {A B C D E : Type}
    {f : A ⟶ B} {g : A ⟶ C} {l : B ⟶ D} {r : C ⟶ D}
    {l' : B ⟶ E} {r' : C ⟶ E} (hD : IsPushout f g l r)
    (hE : IsPushout f g l' r') (m : D ⟶ E)
    (hl : l ≫ m = l') (hr : r ≫ m = r') : Function.Bijective m := by
  let e := hD.isoIsPushout B C hE
  have hm : m = e.hom := hD.hom_ext
    (hl.trans (hD.inl_isoIsPushout_hom B C hE).symm)
    (hr.trans (hD.inr_isoIsPushout_hom B C hE).symm)
  rw [hm]
  exact (isIso_iff_bijective e.hom).mp inferInstance

variable (U : NecklaceCode) (j : Joint U) (P : Over U)

private abbrev endJoint : Joint U := ⟨Fin.last U.len, U.last_mem⟩
private abbrev a := (least P.hom j).val
private abbrev p := (greatest P.hom j).val
private abbrev z := (greatest P.hom (endJoint U)).val

private theorem a_le_p : a U j P ≤ p U j P := le_greatest (least P.hom) j

private theorem a_le_z : a U j P ≤ z U P :=
  (le_greatest_iff P.hom (endJoint U) _).2
    ((least P.hom j).property.symm ▸ Fin.le_last j.val)

private theorem z_eq_last : z U P = Fin.last P.left.len := by
  apply le_antisymm (Fin.le_last _)
  apply (le_greatest_iff P.hom (endJoint U) _).2
  rw [orderMap_last]
  exact Fin.le_last _

/-- The short native right interval embeds into the full right inverse image. -/
def shortToFull : (cutRight P.left (p U j P)).toSSet ⟶
    (sourceInterval P.hom j (endJoint U) (Fin.le_last _)).toSSet :=
  intervalFactor P.left (a U j P) (z U P)
    (a_le_z U j P)
    (cutRightι P.left (p U j P)) (by
      intro x
      have hv := intervalEmbedding_bounds P.left (p U j P) (Fin.last P.left.len)
        (Fin.le_last _) ((cutRight P.left (p U j P)).inclusion.app _ x 0)
      have he := intervalι_apply P.left (p U j P) (Fin.last P.left.len)
        (Fin.le_last _) x (0 : Fin 1)
      change a U j P ≤ P.left.inclusion.app _
          ((intervalι P.left (p U j P) (Fin.last P.left.len) (Fin.le_last _)).app _ x) 0 ∧
        P.left.inclusion.app _
          ((intervalι P.left (p U j P) (Fin.last P.left.len) (Fin.le_last _)).app _ x) 0 ≤
          z U P
      rw [he]
      rw [z_eq_last U P]
      exact ⟨(a_le_p U j P).trans hv.1, hv.2⟩)

theorem shortToFull_fac :
    shortToFull U j P ≫ rightInclusion.{0} P.hom j =
      cutRightι P.left (p U j P) := by
  exact intervalFactor_fac P.left (a U j P) (z U P) _ _ _

/-- The short native right interval is a retract of the full right inverse image. -/
theorem shortToFull_clamp :
    shortToFull U j P ≫ rightInclusion P.hom j ≫
      rightClamp P.left (p U j P) = 𝟙 _ := by
  have : Mono (cutRightι.{0} P.left (p U j P)) :=
    inferInstanceAs (Mono (intervalι P.left (p U j P) (Fin.last P.left.len) (Fin.le_last _)))
  apply (cancel_mono (cutRightι P.left (p U j P))).mp
  rw [Category.id_comp, ← Category.assoc (shortToFull U j P)
    (rightInclusion P.hom j) (rightClamp P.left (p U j P)), shortToFull_fac]
  apply hom_ext_vertices
  funext v
  cases v with
  | up v =>
  apply ULift.ext
  have hi : orderMap (cutRightι P.left (p U j P)) v =
      intervalEmbedding P.left (p U j P) (Fin.last P.left.len) (Fin.le_last _) v :=
    congrArg ULift.down
      (intervalι_vertices P.left (p U j P) (Fin.last P.left.len)
        (Fin.le_last _) (ULift.up v))
  have hb := (intervalEmbedding_bounds P.left (p U j P) (Fin.last P.left.len)
    (Fin.le_last _) v).1
  calc
    _ = orderMap (rightClamp P.left (p U j P) ≫ cutRightι P.left (p U j P))
        (orderMap (cutRightι P.left (p U j P)) v) :=
      orderMap_comp_apply _ _ v
    _ = max (orderMap (cutRightι P.left (p U j P)) v) (p U j P) :=
      rightClamp_orderMap _ _ _
    _ = orderMap (cutRightι P.left (p U j P)) v := max_eq_left (hi.trans_ge hb)

private theorem fullClamp_surjective :
    Function.Surjective (((fromFull U j).app P).left.app (op ⦋0⦌)) := by
  intro y
  let x := (shortToFull U j P).app (op ⦋0⦌) y
  refine ⟨x, ?_⟩
  have h := congrFun (NatTrans.congr_app (shortToFull_clamp U j P) (op ⦋0⦌)) y
  exact h

private abbrev full := sourceInterval P.hom j (endJoint U) (Fin.le_last _)
private abbrev common := sourceInterval P.hom j j le_rfl

private theorem fullOrder (v : Fin ((full U j P).len + 1)) :
    orderMap (rightInclusion.{0} P.hom j) v =
      intervalEmbedding P.left (a U j P) (z U P) (a_le_z U j P) v :=
  congrArg ULift.down
    (intervalι_vertices P.left (a U j P) (z U P) (a_le_z U j P) (ULift.up v))

private theorem commonOrder (v : Fin ((common U j P).len + 1)) :
    orderMap (middleInclusion.{0} P.hom j) v =
      intervalEmbedding P.left (a U j P) (p U j P) (a_le_p U j P) v :=
  congrArg ULift.down
    (intervalι_vertices P.left (a U j P) (p U j P) (a_le_p U j P) (ULift.up v))

private theorem fullBound (v : Fin ((full U j P).len + 1)) :
    a U j P ≤ orderMap (rightInclusion.{0} P.hom j) v ∧
      orderMap (rightInclusion.{0} P.hom j) v ≤ z U P := by
  rw [fullOrder]
  exact intervalEmbedding_bounds P.left (a U j P) (z U P) (a_le_z U j P) v

private theorem commonInFull (x : (full U j P).toSSet.obj (op ⦋0⦌))
    (hx : orderMap (rightInclusion.{0} P.hom j)
      ((full U j P).verticesEquiv x).down ≤ p U j P) :
    x ∈ Set.range ((JTTargetIntervalGluing.middleRight P.hom j).app (op ⦋0⦌)) := by
  let v := ((full U j P).verticesEquiv x).down
  let t := orderMap (rightInclusion.{0} P.hom j) v
  have ht : a U j P ≤ t := (fullBound U j P v).1
  obtain ⟨w, hw⟩ := intervalEmbedding_preimage P.left
    (a U j P) (p U j P) (a_le_p U j P) t ht hx
  let y := (common U j P).verticesEquiv.symm (ULift.up w)
  have he : (middleInclusion.{0} P.hom j).app (op ⦋0⦌) y =
      (rightInclusion.{0} P.hom j).app (op ⦋0⦌) x := by
    apply P.left.verticesEquiv.injective
    apply ULift.ext
    have hy : (P.left.verticesEquiv ((middleInclusion.{0} P.hom j).app _ y)).down =
        orderMap (middleInclusion.{0} P.hom j) w := by
      dsimp [orderMap, mapVertices, y]
      rfl
    have hx' : (P.left.verticesEquiv ((rightInclusion.{0} P.hom j).app _ x)).down =
        orderMap (rightInclusion.{0} P.hom j) v := by
      have hvx : (full U j P).verticesEquiv.symm (ULift.up v) = x := by
        dsimp [v]
        rw [show ULift.up ((full U j P).verticesEquiv x).down =
          (full U j P).verticesEquiv x from by cases (full U j P).verticesEquiv x; rfl]
        exact Equiv.symm_apply_apply _ _
      rw [← hvx]
      rfl
    rw [hy, hx', commonOrder, hw]
  refine ⟨y, ?_⟩
  have hf := congrFun (NatTrans.congr_app (middleRight_fac P.hom j) (op ⦋0⦌)) y
  change (rightInclusion.{0} P.hom j).app _
      ((JTTargetIntervalGluing.middleRight P.hom j).app _ y) =
    (middleInclusion.{0} P.hom j).app _ y at hf
  apply intervalι_injective_app P.left (a U j P) (z U P) (a_le_z U j P) _
  exact hf.trans he

private theorem vertexMapDown {S T : NecklaceCode}
    (h : S.toSSet ⟶ T.toSSet) (x : S.toSSet.obj (op ⦋0⦌)) :
    (T.verticesEquiv (h.app (op ⦋0⦌) x)).down =
      orderMap h (S.verticesEquiv x).down := by
  dsimp [orderMap, mapVertices]
  rw [show ULift.up (S.verticesEquiv x).down = S.verticesEquiv x from by
    cases S.verticesEquiv x; rfl]
  rw [Equiv.symm_apply_apply]

private theorem fullClampOrder (v : Fin ((full U j P).len + 1)) :
    orderMap (((fromFull U j).app P).left ≫
      cutRightι P.left (p U j P)) v =
      max (orderMap (rightInclusion.{0} P.hom j) v) (p U j P) := by
  change orderMap ((rightInclusion.{0} P.hom j ≫
    rightClamp P.left (p U j P)) ≫ cutRightι P.left (p U j P)) v = _
  rw [Category.assoc, orderMap_comp_apply]
  exact rightClamp_orderMap P.left (p U j P) _

private theorem outside_gt (x : (full U j P).toSSet.obj (op ⦋0⦌))
    (hx : x ∉ Set.range ((JTTargetIntervalGluing.middleRight P.hom j).app (op ⦋0⦌))) :
    p U j P < orderMap (rightInclusion.{0} P.hom j)
      ((full U j P).verticesEquiv x).down := by
  exact lt_of_not_ge (fun h ↦ hx (commonInFull U j P x h))

private theorem fullClamp_injective_off_common
    (x y : (full U j P).toSSet.obj (op ⦋0⦌))
    (hx : x ∉ Set.range ((JTTargetIntervalGluing.middleRight P.hom j).app (op ⦋0⦌)))
    (hy : y ∉ Set.range ((JTTargetIntervalGluing.middleRight P.hom j).app (op ⦋0⦌)))
    (he : ((fromFull U j).app P).left.app (op ⦋0⦌) x =
      ((fromFull U j).app P).left.app (op ⦋0⦌) y) : x = y := by
  let vx := ((full U j P).verticesEquiv x).down
  let vy := ((full U j P).verticesEquiv y).down
  have hcoord :
      orderMap (((fromFull U j).app P).left ≫ cutRightι P.left (p U j P)) vx =
      orderMap (((fromFull U j).app P).left ≫ cutRightι P.left (p U j P)) vy := by
    rw [← vertexMapDown _ x, ← vertexMapDown _ y]
    exact congrArg (fun t ↦ (P.left.verticesEquiv
      ((cutRightι P.left (p U j P)).app (op ⦋0⦌) t)).down) he
  rw [fullClampOrder U j P, fullClampOrder U j P] at hcoord
  have hpx := (outside_gt U j P x hx).le
  have hpy := (outside_gt U j P y hy).le
  rw [max_eq_left hpx, max_eq_left hpy, fullOrder U j P, fullOrder U j P] at hcoord
  have hv : vx = vy := (intervalEmbedding P.left (a U j P) (z U P)
    (a_le_z U j P)).injective hcoord
  apply (full U j P).verticesEquiv.injective
  exact ULift.ext _ _ hv

private theorem pointCoord (c : (Δ[0] : SSet.{0}).obj (op ⦋0⦌)) :
    (P.left.verticesEquiv
      (((fromJoint U j).app P).left.app (op ⦋0⦌) c |>
        (cutRightι P.left (p U j P)).app (op ⦋0⦌))).down = p U j P := by
  have h := DaggerOriginalProductGadget.intervalPoint_first P.left (p U j P)
    (Fin.last P.left.len) (Fin.le_last _)
  change pointAt (cutRight P.left (p U j P)) (ULift.up 0) ≫
    cutRightι P.left (p U j P) = pointAt P.left (ULift.up (p U j P)) at h
  have hc := congrFun (NatTrans.congr_app h (op ⦋0⦌)) c
  change (P.left.verticesEquiv
    ((pointAt (cutRight P.left (p U j P)) (ULift.up 0) ≫
      cutRightι P.left (p U j P)).app _ c)).down = p U j P
  rw [hc, pointAt, pointAt_vertex_apply, Equiv.apply_symm_apply]

private theorem fullClamp_point_fiber
    (x : (full U j P).toSSet.obj (op ⦋0⦌))
    (c : (Δ[0] : SSet.{0}).obj (op ⦋0⦌))
    (he : ((fromFull U j).app P).left.app (op ⦋0⦌) x =
      ((fromJoint U j).app P).left.app (op ⦋0⦌) c) :
    ∃ y : (common U j P).toSSet.obj (op ⦋0⦌),
      (JTTargetIntervalGluing.middleRight P.hom j).app (op ⦋0⦌) y = x ∧
      (middlePoint P.hom j).app (op ⦋0⦌) y = c := by
  have hc : orderMap (rightInclusion.{0} P.hom j)
      ((full U j P).verticesEquiv x).down ≤ p U j P := by
    have hv := congrArg (fun t ↦ (P.left.verticesEquiv
      ((cutRightι P.left (p U j P)).app (op ⦋0⦌) t)).down) he
    change (P.left.verticesEquiv
      ((((fromFull U j).app P).left ≫ cutRightι P.left (p U j P)).app _ x)).down =
      (P.left.verticesEquiv
      ((((fromJoint U j).app P).left ≫ cutRightι P.left (p U j P)).app _ c)).down at hv
    rw [vertexMapDown, fullClampOrder U j P] at hv
    have hp := pointCoord U j P c
    change (P.left.verticesEquiv
      ((((fromJoint U j).app P).left ≫ cutRightι P.left (p U j P)).app _ c)).down =
      p U j P at hp
    rw [hp] at hv
    exact (max_le_iff.mp hv.le).1
  obtain ⟨y, hy⟩ := commonInFull U j P x hc
  refine ⟨y, hy, ?_⟩
  exact (zeroSimplex_unique _).trans (zeroSimplex_unique _).symm

private theorem quotient_isPushout_vertex :
    IsPushout
      (((overlapToRight U j).app P).left.app (op ⦋0⦌))
      (((overlapToJoint U j).app P).left.app (op ⦋0⦌))
      (((rightCollapse U j).app P).left.app (op ⦋0⦌))
      (((jointToRight U j).app P).left.app (op ⦋0⦌)) := by
  let E := ((evaluation (Over U) (Over U.toSSet)).obj P ⋙
    Over.forget U.toSSet) ⋙
    (evaluation SimplexCategoryᵒᵖ (Type)).obj (op ⦋0⦌)
  have h := (IsPushout.of_hasPushout (overlapToRight U j)
    (overlapToJoint U j)).map E
  convert h using 1

private theorem clipped_isPushout_vertex :
    IsPushout
      (((overlapToRight U j).app P).left.app (op ⦋0⦌))
      (((overlapToJoint U j).app P).left.app (op ⦋0⦌))
      (((fromFull U j).app P).left.app (op ⦋0⦌))
      (((fromJoint U j).app P).left.app (op ⦋0⦌)) := by
  have hf : Function.Injective
      (((overlapToRight U j).app P).left.app (op ⦋0⦌)) := by
    have hmi : Mono (middleInclusion P.hom j) := by
      unfold middleInclusion sourceInclusion
      infer_instance
    have hmr : Mono (JTTargetIntervalGluing.middleRight P.hom j) :=
      mono_of_mono_fac (middleRight_fac P.hom j)
    exact (mono_iff_injective _).mp
      ((NatTrans.mono_iff_mono_app _).mp hmr (op ⦋0⦌))
  have hs : Function.Injective
      (((fromJoint U j).app P).left.app (op ⦋0⦌)) := by
    intro x y _
    exact (zeroSimplex_unique x).trans (zeroSimplex_unique y).symm
  have hw := congrArg (fun t : overlap U j ⟶ clipped U j ↦
    ((t.app P).left).app (op ⦋0⦌)) (overlap_eq U j)
  change ((overlapToRight U j).app P).left.app (op ⦋0⦌) ≫
      ((fromFull U j).app P).left.app (op ⦋0⦌) =
    ((overlapToJoint U j).app P).left.app (op ⦋0⦌) ≫
      ((fromJoint U j).app P).left.app (op ⦋0⦌) at hw
  exact type_isPushout_of_clamp _ _ _ _ hf hs hw
    (fullClamp_surjective U j P) (fullClamp_point_fiber U j P)
    (fullClamp_injective_off_common U j P)

/-- The right quotient comparison is bijective on degree-zero simplices. -/
theorem fromQuotient_vertices_bijective :
    Function.Bijective (((fromQuotient U j).app P).left.app (op ⦋0⦌)) := by
  have hl := congrArg (fun t : right U j ⟶ clipped U j ↦
    ((t.app P).left).app (op ⦋0⦌)) (collapse_fromQuotient U j)
  have hr := congrArg (fun t : joint U j ⟶ clipped U j ↦
    ((t.app P).left).app (op ⦋0⦌)) (joint_fromQuotient U j)
  change ((rightCollapse U j).app P).left.app (op ⦋0⦌) ≫
      ((fromQuotient U j).app P).left.app (op ⦋0⦌) =
    ((fromFull U j).app P).left.app (op ⦋0⦌) at hl
  change ((jointToRight U j).app P).left.app (op ⦋0⦌) ≫
      ((fromQuotient U j).app P).left.app (op ⦋0⦌) =
    ((fromJoint U j).app P).left.app (op ⦋0⦌) at hr
  exact type_bijective_of_pushout_comparison
    (quotient_isPushout_vertex U j P) (clipped_isPushout_vertex U j P)
    _ hl hr

end

end DaggerModels.PartII.JTJointClippedRightVertices
