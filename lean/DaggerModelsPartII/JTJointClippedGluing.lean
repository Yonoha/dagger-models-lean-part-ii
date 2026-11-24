import DaggerModelsPartII.JTJointClippedSideComparison
import DaggerModelsPartII.JTJointClippedRightComparison
import DaggerModelsPartII.LeftProperPushoutComparison
import ChosenNecklaceWedgeFunctor

/-! The joint quotient compares weakly to the native clipped wedge over the original target. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTJointClippedGluing

open JTTargetJointMarks (Joint)
open JTJointIntervalQuotient (joint jointToLeft jointToRight leftLeg rightLeg wholeQuotient
  quotients_isPushout wholeCollapse wholeCollapse_app_weak)
open JTJointClippedSideComparison (jointToNativeLeft fromLeftQuotient jointToLeft_fromLeftQuotient)
open JTJointClippedSides (leftNative rightNative)

noncomputable section

variable (U : NecklaceCode) (j : Joint U)

private abbrev R := JTJointClippedRightComparison.fromJoint U j
private abbrev rightComparison := JTJointClippedRightComparison.fromQuotient U j

/-- Glue the two short native sides at the same fixed joint point over the original target. -/
def glued : Over U ⥤ Over U.toSSet :=
  pushout (jointToNativeLeft U j) (R U j)

private abbrev inl := pushout.inl (jointToNativeLeft U j) (R U j)
private abbrev inr := pushout.inr (jointToNativeLeft U j) (R U j)

theorem glued_isPushout :
    IsPushout (jointToNativeLeft U j) (R U j) (inl U j) (inr U j) :=
  IsPushout.of_hasPushout _ _

/-- The whole actual quotient compares to the glued short sides, over the same target. -/
def compare : wholeQuotient U j ⟶ glued U j :=
  (quotients_isPushout U j).desc (fromLeftQuotient U j ≫ inl U j)
    (rightComparison U j ≫ inr U j) (by
      rw [← Category.assoc, ← Category.assoc,
        jointToLeft_fromLeftQuotient, JTJointClippedRightComparison.joint_fromQuotient]
      exact (glued_isPushout U j).w)

@[reassoc]
theorem compare_left : leftLeg U j ≫ compare U j = fromLeftQuotient U j ≫ inl U j :=
  (quotients_isPushout U j).inl_desc _ _ _

@[reassoc]
theorem compare_right : rightLeg U j ≫ compare U j = rightComparison U j ≫ inr U j :=
  (quotients_isPushout U j).inr_desc _ _ _

private abbrev underlyingAt (P : Over U) :=
  (evaluation (Over U) (Over U.toSSet)).obj P ⋙ Over.forget U.toSSet

/-- In each original source the glued short sides have their native wedge as a model. -/
def wedgeIso (P : Over U) : ((glued U j).obj P).left ≅
    (NecklaceCode.wedge ((leftNative U j).obj P).left ((rightNative U j).obj P).left).toSSet :=
  ((glued_isPushout U j).map (underlyingAt U P)).isoIsPushout _ _
    (NecklaceCode.wedgeIsPushout ((leftNative U j).obj P).left ((rightNative U j).obj P).left)

private theorem jointCofibration {X : SSet.{0}} (p : (Δ[0] : SSet.{0}) ⟶ X) :
    cofibrations SSet.{0} p := by
  haveI : Mono p := SSet.stdSimplex.isTerminalObj₀.mono_from p
  exact (cofibration_iff _).mp ((SSet.modelCategoryQuillen.cofibration_iff _).mpr inferInstance)

/-- The actual comparison is Kan weak on every original source. -/
theorem compare_app_weak (P : Over U) : WeakEquivalence ((compare U j).app P).left := by
  let E := underlyingAt U P
  have sq := (quotients_isPushout U j).map E
  have sq' := (glued_isPushout U j).map E
  have h₁ : E.map (jointToLeft U j) ≫ E.map (fromLeftQuotient U j) =
      𝟙 _ ≫ E.map (jointToNativeLeft U j) := by
    rw [← E.map_comp, jointToLeft_fromLeftQuotient, Category.id_comp]
  have h₂ : E.map (jointToRight U j) ≫ E.map (rightComparison U j) =
      𝟙 _ ≫ E.map (R U j) := by
    rw [← E.map_comp, JTJointClippedRightComparison.joint_fromQuotient, Category.id_comp]
  have h₃ : E.map (leftLeg U j) ≫ E.map (compare U j) =
      E.map (fromLeftQuotient U j) ≫ E.map (inl U j) := by
    rw [← E.map_comp, ← E.map_comp, compare_left]
  have h₄ : E.map (rightLeg U j) ≫ E.map (compare U j) =
      E.map (rightComparison U j) ≫ E.map (inr U j) := by
    rw [← E.map_comp, ← E.map_comp, compare_right]
  exact (weakEquivalence_iff _).mpr (weak_of_pushoutComparison
    (fun s h₁ h₂ ↦ kanLeftProper s h₁ h₂) sq sq'
    (jointCofibration (E.map (jointToLeft U j))) (jointCofibration (E.map (jointToNativeLeft U j)))
    (𝟙 _) (E.map (fromLeftQuotient U j)) (E.map (rightComparison U j)) (E.map (compare U j))
    h₁ h₂ h₃ h₄ ((weakEquivalence_iff _).mp inferInstance)
    ((weakEquivalence_iff _).mp (JTJointClippedSideComparison.fromLeftQuotient_app_weak U j P))
    ((weakEquivalence_iff _).mp (JTJointClippedRightComparison.fromQuotient_app_weak U j P)))

/-- The full original source maps to the glued clipped sides by a Kan weak comparison. -/
theorem fromOriginal_app_weak (P : Over U) :
    WeakEquivalence (((wholeCollapse U j ≫ compare U j).app P).left) := by
  change WeakEquivalence (((wholeCollapse U j).app P).left ≫ ((compare U j).app P).left)
  letI := wholeCollapse_app_weak U j P
  letI := compare_app_weak U j P
  infer_instance


open JTJointRelativeParameters (withTimeMap withTimeMap_app)
open DaggerSSetGluing

/-- The native comparison retains the weak type of the total simplices, with arbitrary time. -/
theorem timed_fromOriginal_total_weak {X : SSet.{0}} (q : U.toSSet ⟶ X)
    {I : Type} [SmallCategory I] (K : SimplexCategory ⥤ SSet.{0})
    (time : I ⥤ SimplexCategory) (D : I ⥤ Over U) :
    WeakEquivalence (nerveMap (TotalElementsWeakComparison.totalMap
      (withTimeMap q K time D (wholeCollapse U j ≫ compare U j)))) := by
  apply TotalElementsWeakComparison.totalMap_weak
  intro a
  rw [withTimeMap_app]
  exact (weakEquivalence_iff_GW _).mpr (DaggerSSetProductGeometric.tensorMap_geometric _ _
    ((weakEquivalence_iff_GW _).mp (fromOriginal_app_weak U j (D.obj a)))
    (DaggerSSetProductGeometric.identity_geometric _))

private abbrev zero := op (⦋0⦌ : SimplexCategory)

/-- The comparisons of the two sides determine the comparison on degree zero. -/
theorem compare_vertex_isIso_of_sides (P : Over U)
    (hL : IsIso (((fromLeftQuotient U j).app P).left.app zero))
    (hR : IsIso (((rightComparison U j).app P).left.app zero)) :
    IsIso (((compare U j).app P).left.app zero) := by
  let E := underlyingAt U P ⋙ (evaluation SimplexCategoryᵒᵖ (Type 0)).obj zero
  let b := E.map (fromLeftQuotient U j)
  let c := E.map (rightComparison U j)
  letI : IsIso b := hL
  letI : IsIso c := hR
  let d := E.map (compare U j)
  have sq := (quotients_isPushout U j).map E
  have sq' := (glued_isPushout U j).map E
  have hb : E.map (jointToLeft U j) ≫ b = E.map (jointToNativeLeft U j) := by
    change _ ≫ E.map (fromLeftQuotient U j) = _
    rw [← E.map_comp, jointToLeft_fromLeftQuotient]
  have hc : E.map (jointToRight U j) ≫ c = E.map (R U j) := by
    change _ ≫ E.map (rightComparison U j) = _
    rw [← E.map_comp, JTJointClippedRightComparison.joint_fromQuotient]
  have h₁ : E.map (leftLeg U j) ≫ d = b ≫ E.map (inl U j) := by
    change _ ≫ E.map (compare U j) = E.map (fromLeftQuotient U j) ≫ _
    rw [← E.map_comp, ← E.map_comp, compare_left]
  have h₂ : E.map (rightLeg U j) ≫ d = c ≫ E.map (inr U j) := by
    change _ ≫ E.map (compare U j) = E.map (rightComparison U j) ≫ _
    rw [← E.map_comp, ← E.map_comp, compare_right]
  have sq'' := sq'.of_iso' (Iso.refl _) (asIso b) (asIso c) (Iso.refl _)
    (f' := E.map (jointToLeft U j)) (g' := E.map (jointToRight U j))
    (inl' := E.map (leftLeg U j) ≫ d) (inr' := E.map (rightLeg U j) ≫ d)
    (by simpa only [Iso.refl_hom, Category.id_comp] using hb.symm)
    (by simpa only [Iso.refl_hom, Category.id_comp] using hc.symm)
    (by simpa only [Iso.refl_hom, Category.comp_id] using h₁.symm)
    (by simpa only [Iso.refl_hom, Category.comp_id] using h₂.symm)
  have hd : (sq.isoIsPushout _ _ sq'').hom = d := by
    apply sq.hom_ext
    · exact IsPushout.inl_isoIsPushout_hom _ _ sq sq''
    · exact IsPushout.inr_isoIsPushout_hom _ _ sq sq''
  change IsIso d
  rw [← hd]
  infer_instance

section Native

open NecklaceCode (wedge wedgeMap wedgeIsPushout wedgeιLeft wedgeιRight)
open JTJointClippedSides (leftObj_fac rightObj_fac leftSourceOver rightSourceOver)

private abbrev leftCode (P : Over U) := ((leftNative U j).obj P).left
private abbrev rightCode (P : Over U) := ((rightNative U j).obj P).left
private abbrev nativeWedge (P : Over U) :=
  NecklacesOver.wedge (leftSourceOver U j P) (rightSourceOver U j P)

private def nativeCollapse (P : Over U) : wedge (leftCode U j P) (rightCode U j P) ⟶ U where
  map := (nativeWedge U j P).map
  first := (nativeWedge U j P).first
  last := (nativeWedge U j P).last

private theorem left_nativeCollapse (P : Over U) :
    wedgeιLeft (leftCode U j P) (rightCode U j P) ≫ (nativeCollapse U j P).map =
      ((leftNative U j).obj P).hom.map ≫ NecklaceCode.cutLeftι U j.val :=
  (NecklacesOver.wedge_left _ _).trans (leftObj_fac U j P).symm

private theorem right_nativeCollapse (P : Over U) :
    wedgeιRight (leftCode U j P) (rightCode U j P) ≫ (nativeCollapse U j P).map =
      ((rightNative U j).obj P).hom.map ≫ NecklaceCode.cutRightι U j.val :=
  (NecklacesOver.wedge_right _ _).trans (rightObj_fac U j P).symm

set_option maxHeartbeats 700000 in
private theorem nativeCollapse_naturality {P P' : Over U} (g : P ⟶ P') :
    (wedgeMap ((leftNative U j).map g).left ((rightNative U j).map g).left) ≫
      nativeCollapse U j P' = nativeCollapse U j P := by
  apply NecklaceCode.Hom.ext
  apply (wedgeIsPushout (leftCode U j P) (rightCode U j P)).hom_ext
  · change _ ≫ ((wedgeMap ((leftNative U j).map g).left
      ((rightNative U j).map g).left).map ≫ (nativeCollapse U j P').map) = _
    rw [← Category.assoc, NecklaceCode.wedgeMap_left, Category.assoc,
      left_nativeCollapse, left_nativeCollapse, ← Category.assoc]
    have h := congrArg NecklaceCode.Hom.map (Over.w ((leftNative U j).map g))
    exact congrArg (fun a ↦ a ≫ NecklaceCode.cutLeftι U j.val) h
  · change _ ≫ ((wedgeMap ((leftNative U j).map g).left
      ((rightNative U j).map g).left).map ≫ (nativeCollapse U j P').map) = _
    rw [← Category.assoc, NecklaceCode.wedgeMap_right, Category.assoc,
      right_nativeCollapse, right_nativeCollapse, ← Category.assoc]
    have h := congrArg NecklaceCode.Hom.map (Over.w ((rightNative U j).map g))
    exact congrArg (fun a ↦ a ≫ NecklaceCode.cutRightι U j.val) h

/-- The actual wedged necklace is functorial as a native necklace over the
original target. -/
def nativeGlued : Over U ⥤ Over U where
  obj P := Over.mk (nativeCollapse U j P)
  map g := Over.homMk (wedgeMap ((leftNative U j).map g).left ((rightNative U j).map g).left)
    (nativeCollapse_naturality U j g)
  map_id P := by
    ext1
    change wedgeMap ((leftNative U j).map (𝟙 P)).left ((rightNative U j).map (𝟙 P)).left = _
    rw [(leftNative U j).map_id, (rightNative U j).map_id]
    exact NecklaceCode.wedgeMap_id
  map_comp f g := by
    ext1
    simp only [Functor.map_comp]
    exact NecklaceCode.wedgeMap_comp _ _ _ _

@[reassoc]
theorem inl_wedgeIso_hom (P : Over U) :
    ((inl U j).app P).left ≫ (wedgeIso U j P).hom =
      wedgeιLeft (leftCode U j P) (rightCode U j P) :=
  IsPushout.inl_isoIsPushout_hom _ _ ((glued_isPushout U j).map (underlyingAt U P))
    (wedgeIsPushout (leftCode U j P) (rightCode U j P))

@[reassoc]
theorem inr_wedgeIso_hom (P : Over U) :
    ((inr U j).app P).left ≫ (wedgeIso U j P).hom =
      wedgeιRight (leftCode U j P) (rightCode U j P) :=
  IsPushout.inr_isoIsPushout_hom _ _ ((glued_isPushout U j).map (underlyingAt U P))
    (wedgeIsPushout (leftCode U j P) (rightCode U j P))

/-- The pointwise pushout isomorphisms identify the glued diagram with the
native wedge diagram, naturally and in the original slice. -/
def gluedIsoNative : glued U j ≅ nativeGlued U j ⋙ Over.post NecklaceCode.simplicialFunctor :=
  NatIso.ofComponents (fun P ↦ Over.isoMk (wedgeIso U j P) (by
    change (wedgeIso U j P).hom ≫ (nativeCollapse U j P).map = ((glued U j).obj P).hom
    apply ((glued_isPushout U j).map (underlyingAt U P)).hom_ext
    · change ((inl U j).app P).left ≫ _ = _
      rw [inl_wedgeIso_hom_assoc, left_nativeCollapse]
      exact (Over.w ((inl U j).app P)).symm
    · change ((inr U j).app P).left ≫ _ = _
      rw [inr_wedgeIso_hom_assoc, right_nativeCollapse]
      exact (Over.w ((inr U j).app P)).symm))
    (by
      intro P P' g
      apply Over.OverMorphism.ext
      apply ((glued_isPushout U j).map (underlyingAt U P)).hom_ext
      · have h := congrArg (fun f ↦ f.left) ((inl U j).naturality g)
        change ((leftNative U j).map g).left.map ≫ ((inl U j).app P').left =
          ((inl U j).app P).left ≫ ((glued U j).map g).left at h
        change ((inl U j).app P).left ≫ (((glued U j).map g).left ≫ (wedgeIso U j P').hom) =
          ((inl U j).app P).left ≫ ((wedgeIso U j P).hom ≫
            (wedgeMap ((leftNative U j).map g).left ((rightNative U j).map g).left).map)
        rw [← Category.assoc, ← h, Category.assoc, inl_wedgeIso_hom,
          inl_wedgeIso_hom_assoc, NecklaceCode.wedgeMap_left]
      · have h := congrArg (fun f ↦ f.left) ((inr U j).naturality g)
        change ((rightNative U j).map g).left.map ≫ ((inr U j).app P').left =
          ((inr U j).app P).left ≫ ((glued U j).map g).left at h
        change ((inr U j).app P).left ≫ (((glued U j).map g).left ≫ (wedgeIso U j P').hom) =
          ((inr U j).app P).left ≫ ((wedgeIso U j P).hom ≫
            (wedgeMap ((leftNative U j).map g).left ((rightNative U j).map g).left).map)
        rw [← Category.assoc, ← h, Category.assoc, inr_wedgeIso_hom,
          inr_wedgeIso_hom_assoc, NecklaceCode.wedgeMap_right])

open NecklaceCode (pointAt pointAt_comp orderMap cutLeftι cutRightι)
open JTTargetJointMarks (least greatest)
open JTNativeIntervalClamp (leftClamp rightClamp leftClamp_orderMap rightClamp_orderMap)
open JTTargetIntervalGluing (leftInclusion rightInclusion)
open JTTargetIntervalOverMapping (whole leftToWhole rightToWhole)
open DaggerOriginalProductGadget (intervalPoint_first intervalPoint_last)

/-- The complete original collapse comparison in the original simplicial slice. -/
def simplicialComparison :
    whole U ⟶ nativeGlued U j ⋙ Over.post NecklaceCode.simplicialFunctor :=
  wholeCollapse U j ≫ compare U j ≫ (gluedIsoNative U j).hom

private theorem left_comparison' :
    leftToWhole U j ≫ simplicialComparison U j =
      JTJointClippedSideComparison.fromFullLeft U j ≫
        inl U j ≫ (gluedIsoNative U j).hom := by
  unfold simplicialComparison
  rw [← JTJointIntervalQuotient.leftCollapse_leg_assoc, compare_left_assoc,
    JTJointClippedSideComparison.leftCollapse_fromLeftQuotient_assoc]

private theorem right_comparison' :
    rightToWhole U j ≫ simplicialComparison U j =
      JTJointClippedRightComparison.fromFull U j ≫ inr U j ≫ (gluedIsoNative U j).hom := by
  unfold simplicialComparison
  rw [← JTJointIntervalQuotient.rightCollapse_leg_assoc, compare_right_assoc,
    JTJointClippedRightComparison.collapse_fromQuotient_assoc]

theorem simplicialComparison_left (P : Over U) :
    leftInclusion P.hom j ≫ ((simplicialComparison U j).app P).left =
      (leftInclusion P.hom j ≫ leftClamp P.left (least P.hom j).val) ≫
        wedgeιLeft (leftCode U j P) (rightCode U j P) := by
  have h := congrArg (fun f ↦ f.left) (NatTrans.congr_app (left_comparison' U j) P)
  change _ = (leftInclusion P.hom j ≫ leftClamp P.left (least P.hom j).val) ≫
    ((inl U j).app P).left ≫ (wedgeIso U j P).hom at h
  rw [inl_wedgeIso_hom] at h
  exact h

theorem simplicialComparison_right (P : Over U) :
    rightInclusion P.hom j ≫ ((simplicialComparison U j).app P).left =
      (rightInclusion P.hom j ≫ rightClamp P.left (greatest P.hom j).val) ≫
        wedgeιRight (leftCode U j P) (rightCode U j P) := by
  have h := congrArg (fun f ↦ f.left) (NatTrans.congr_app (right_comparison' U j) P)
  change _ = (rightInclusion P.hom j ≫ rightClamp P.left (greatest P.hom j).val) ≫
    ((inr U j).app P).left ≫ (wedgeIso U j P).hom at h
  rw [inr_wedgeIso_hom] at h
  exact h

private theorem clamp_first (T : NecklaceCode) (c : Fin (T.len + 1)) :
    pointAt T (ULift.up 0) ≫ leftClamp T c =
      pointAt (NecklaceCode.cutLeft T c) (ULift.up 0) := by
  have : Mono (cutLeftι.{0} T c) :=
    inferInstanceAs (Mono (NecklaceCode.intervalι T 0 c (Fin.zero_le c)))
  apply (cancel_mono (cutLeftι T c)).mp
  have he : pointAt (NecklaceCode.cutLeft T c) (ULift.up 0) ≫ cutLeftι T c =
      pointAt T (ULift.up 0) := intervalPoint_first T 0 c (Fin.zero_le c)
  rw [Category.assoc, he, pointAt_comp]
  apply congrArg (pointAt T)
  apply ULift.ext
  exact (leftClamp_orderMap T c 0).trans (min_eq_left (Fin.zero_le c))

private theorem clamp_last (T : NecklaceCode) (c : Fin (T.len + 1)) :
    pointAt T (ULift.up (Fin.last T.len)) ≫ rightClamp T c =
      pointAt (NecklaceCode.cutRight T c)
        (ULift.up (Fin.last (NecklaceCode.cutRight T c).len)) := by
  have : Mono (cutRightι.{0} T c) :=
    inferInstanceAs (Mono (NecklaceCode.intervalι T c (Fin.last T.len) (Fin.le_last c)))
  apply (cancel_mono (cutRightι T c)).mp
  have he : pointAt (NecklaceCode.cutRight T c)
      (ULift.up (Fin.last (NecklaceCode.cutRight T c).len)) ≫ cutRightι T c =
      pointAt T (ULift.up (Fin.last T.len)) :=
    intervalPoint_last T c (Fin.last T.len) (Fin.le_last c)
  rw [Category.assoc, he, pointAt_comp]
  apply congrArg (pointAt T)
  apply ULift.ext
  exact (rightClamp_orderMap T c (Fin.last T.len)).trans (max_eq_left (Fin.le_last c))

private theorem comparison_first (P : Over U) :
    pointAt P.left (ULift.up 0) ≫ ((simplicialComparison U j).app P).left =
      pointAt (wedge (leftCode U j P) (rightCode U j P)) (ULift.up 0) := by
  let T := JTTargetIntervalPullback.sourceInterval P.hom ⟨0, U.first_mem⟩ j (Fin.zero_le _)
  have h : pointAt T (ULift.up 0) ≫ leftInclusion P.hom j = pointAt P.left (ULift.up 0) :=
    JTTargetIntervalOverMapping.left_first U j P
  rw [← h, Category.assoc, simplicialComparison_left]
  rw [Category.assoc, ← Category.assoc (pointAt T (ULift.up 0)), h]
  rw [← Category.assoc (pointAt P.left (ULift.up 0)), clamp_first]
  exact NecklaceCode.pointAt_first_left _ _

private theorem comparison_last (P : Over U) :
    pointAt P.left (ULift.up (Fin.last P.left.len)) ≫ ((simplicialComparison U j).app P).left =
      pointAt (wedge (leftCode U j P) (rightCode U j P)) (ULift.up (Fin.last _)) := by
  let T := JTTargetIntervalPullback.sourceInterval P.hom j
    ⟨Fin.last U.len, U.last_mem⟩ (Fin.le_last _)
  have h : pointAt T (ULift.up (Fin.last T.len)) ≫ rightInclusion P.hom j =
      pointAt P.left (ULift.up (Fin.last P.left.len)) :=
    JTTargetIntervalOverMapping.right_last U j P
  rw [← h, Category.assoc, simplicialComparison_right]
  rw [Category.assoc, ← Category.assoc (pointAt T (ULift.up (Fin.last T.len))), h]
  rw [← Category.assoc (pointAt P.left (ULift.up (Fin.last P.left.len))), clamp_last]
  exact NecklaceCode.pointAt_last_right _ _

/-- The actual whole comparison preserves the original endpoints and is a
natural transformation of native necklaces over the original target. -/
def nativeComparison : 𝟭 (Over U) ⟶ nativeGlued U j where
  app P := Over.homMk
    { map := ((simplicialComparison U j).app P).left
      first := NecklaceCode.first_of_point _ (comparison_first U j P)
      last := NecklaceCode.last_of_point _ (comparison_last U j P) }
    (by
      apply NecklaceCode.Hom.ext
      exact Over.w ((simplicialComparison U j).app P))
  naturality P P' g := by
    apply Over.OverMorphism.ext
    apply NecklaceCode.Hom.ext
    exact congrArg (fun a ↦ a.left) ((simplicialComparison U j).naturality g)

end Native
end
end DaggerModels.PartII.JTJointClippedGluing
