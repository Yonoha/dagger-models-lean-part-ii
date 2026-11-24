import DaggerModelsPartII.JTTargetIntervalPullback
import OriginalProductPlateau
import Mathlib.CategoryTheory.Adhesive

/-!
# Gluing the native interval preimages at a target joint

Pulling the target joint cut back along the entire native map gives a
pushout. The two source sides overlap in the complete source interval
over the target joint, including any positive-length plateau.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTTargetIntervalGluing

open NecklaceCode JTTargetJointMarks JTTargetIntervalPullback
open DaggerOriginalProductGadget (intervalPoint_first intervalPoint_last)

noncomputable section

private abbrev firstJoint (U : NecklaceCode) : Joint U := ⟨0, U.first_mem⟩
private abbrev lastJoint (U : NecklaceCode) : Joint U := ⟨Fin.last U.len, U.last_mem⟩

variable {T U : NecklaceCode} (f : Hom.{0} T U) (j : Joint U)

/-- The entire left inverse image, including the common interval. -/
abbrev leftInclusion := sourceInclusion f (firstJoint U) j (Fin.zero_le j.val)

/-- The entire right inverse image, including the common interval. -/
abbrev rightInclusion := sourceInclusion f j (lastJoint U) (Fin.le_last j.val)

/-- The whole inverse image of the target joint. -/
abbrev middleInclusion := sourceInclusion f j j le_rfl

private abbrev leftRestrict := restrict f (firstJoint U) j (Fin.zero_le j.val)
private abbrev rightRestrict := restrict f j (lastJoint U) (Fin.le_last j.val)

private def jointIntervalIso (U : NecklaceCode) (j : Joint U) :
    toSSet.{0} (intervalCode U j.val j.val le_rfl) ≅ Δ[0] :=
  eqToIso (congrArg (fun V : NecklaceCode ↦ toSSet.{0} V)
    ((intervalCode_diagonal U j.val).trans (code_eq_point_of_zero (single 0) rfl).symm)) ≪≫
      singleIso 0

private theorem jointIntervalIso_fac (U : NecklaceCode) (j : Joint U) :
    (jointIntervalIso U j).hom ≫ pointAt U (ULift.up j.val) = intervalι U j.val j.val le_rfl := by
  have hp : (jointIntervalIso U j).inv =
      pointAt (intervalCode U j.val j.val le_rfl) (ULift.up 0) :=
    (SSet.stdSimplex.isTerminalObj₀.ofIso (jointIntervalIso U j).symm).hom_ext _ _
  rw [← intervalPoint_first U j.val j.val le_rfl, ← hp, ← Category.assoc,
    Iso.hom_inv_id, Category.id_comp]

/-- The full source overlap maps to the literal target joint point. -/
abbrev middlePoint : (sourceInterval f j j le_rfl).toSSet ⟶ Δ[0] := restrict f j j le_rfl ≫ (jointIntervalIso U j).hom

/-- The full source overlap is the pullback of the original target joint. -/
theorem middlePB :
    IsPullback (middleInclusion f j) (middlePoint f j) f.map (pointAt U (ULift.up j.val)) := by
  have h : IsPullback (intervalι U j.val j.val le_rfl) (jointIntervalIso U j).hom
      (𝟙 (toSSet.{0} U)) (pointAt U (ULift.up j.val)) :=
    IsPullback.of_vert_isIso ⟨(Category.comp_id _).trans (jointIntervalIso_fac U j).symm⟩
  simpa only [Category.comp_id] using (JTTargetIntervalPullback.isPullback f j j le_rfl).paste_vert h

private theorem leftPB :
    IsPullback (leftInclusion f j) (leftRestrict f j) f.map (cutLeftι U j.val) :=
  JTTargetIntervalPullback.isPullback f (firstJoint U) j (Fin.zero_le j.val)

private theorem rightPB :
    IsPullback (rightInclusion f j) (rightRestrict f j) f.map (cutRightι U j.val) :=
  JTTargetIntervalPullback.isPullback f j (lastJoint U) (Fin.le_last j.val)

private abbrev leftPoint (U : NecklaceCode) (j : Joint U) :=
  pointAt (cutLeft U j.val) (ULift.up (Fin.last (cutLeft U j.val).len))

private abbrev rightPoint (U : NecklaceCode) (j : Joint U) :=
  pointAt (cutRight U j.val) (ULift.up 0)

private theorem leftPoint_fac (U : NecklaceCode) (j : Joint U) :
    leftPoint U j ≫ cutLeftι.{0} U j.val = pointAt U (ULift.up j.val) :=
  intervalPoint_last U 0 j.val (Fin.zero_le j.val)

private theorem rightPoint_fac (U : NecklaceCode) (j : Joint U) :
    rightPoint U j ≫ cutRightι.{0} U j.val = pointAt U (ULift.up j.val) :=
  intervalPoint_first U j.val (Fin.last U.len) (Fin.le_last j.val)

/-- The inclusion from the whole common interval into the left interval. -/
def middleLeft : (sourceInterval f j j le_rfl).toSSet ⟶
    (sourceInterval f (firstJoint U) j (Fin.zero_le j.val)).toSSet :=
  (leftPB f j).lift (middleInclusion f j) (middlePoint f j ≫ leftPoint U j) (by
    rw [Category.assoc, leftPoint_fac]
    exact (middlePB f j).w)

/-- The inclusion from the whole common interval into the right interval. -/
def middleRight : (sourceInterval f j j le_rfl).toSSet ⟶
    (sourceInterval f j (lastJoint U) (Fin.le_last j.val)).toSSet :=
  (rightPB f j).lift (middleInclusion f j) (middlePoint f j ≫ rightPoint U j) (by
    rw [Category.assoc, rightPoint_fac]
    exact (middlePB f j).w)

@[reassoc]
theorem middleLeft_fac : middleLeft f j ≫ leftInclusion f j = middleInclusion f j :=
  (leftPB f j).lift_fst _ _ _

@[reassoc]
theorem middleRight_fac : middleRight f j ≫ rightInclusion f j = middleInclusion f j :=
  (rightPB f j).lift_fst _ _ _

private theorem leftBack :
    IsPullback (middleLeft f j) (middlePoint f j) (leftRestrict f j) (leftPoint U j) := by
  have h : IsPullback (middleLeft f j ≫ leftInclusion f j) (middlePoint f j) f.map
      (leftPoint U j ≫ cutLeftι U j.val) := by
    rw [middleLeft_fac, leftPoint_fac]
    exact middlePB f j
  exact h.of_right ((leftPB f j).lift_snd _ _ _) (leftPB f j)

private theorem rightBack :
    IsPullback (middleRight f j) (middlePoint f j) (rightRestrict f j) (rightPoint U j) := by
  have h : IsPullback (middleRight f j ≫ rightInclusion f j) (middlePoint f j) f.map
      (rightPoint U j ≫ cutRightι U j.val) := by
    rw [middleRight_fac, rightPoint_fac]
    exact middlePB f j
  exact h.of_right ((rightPB f j).lift_snd _ _ _) (rightPB f j)

/-- The whole source necklace is the pushout of the two overlapping inverse-image intervals. -/
theorem isPushout :
    IsPushout (middleLeft f j) (middleRight f j) (leftInclusion f j) (rightInclusion f j) := by
  letI : Adhesive SSet.{0} := inferInstanceAs (Adhesive (SimplexCategoryᵒᵖ ⥤ Type))
  letI : Mono (leftPoint U j : Δ[0] ⟶ toSSet.{0} (cutLeft U j.val)) :=
    SSet.stdSimplex.isTerminalObj₀.mono_from _
  exact (Adhesive.van_kampen (cutIsPushout U j.val j.property)
    (middleLeft f j) (middleRight f j) (leftInclusion f j) (rightInclusion f j)
    (middlePoint f j) (leftRestrict f j) (rightRestrict f j) f.map
    (leftBack f j) (rightBack f j) ⟨(leftPB f j).w⟩ ⟨(rightPB f j).w⟩
    ⟨(middleLeft_fac f j).trans (middleRight_fac f j).symm⟩).2
      ⟨leftPB f j, rightPB f j⟩

section Naturality

local instance : SmallCategory NecklaceCode := NecklaceCode.category

variable {T' : NecklaceCode} {f' : T' ⟶ U} (g : T ⟶ T') (hg : g ≫ f' = f)

/-- The left overlap inclusion is natural for an actual native over-target arrow. -/
theorem middleLeft_natural :
    sourceMap f j j le_rfl g hg ≫ middleLeft f' j =
      middleLeft f j ≫ sourceMap f (firstJoint U) j (Fin.zero_le j.val) g hg := by
  letI : Mono (leftInclusion f' j) := by
    unfold leftInclusion sourceInclusion
    infer_instance
  apply (cancel_mono (leftInclusion f' j)).mp
  simp only [Category.assoc, middleLeft_fac, middleLeft_fac_assoc, sourceMap_fac]

/-- The right overlap inclusion is natural for an actual native over-target arrow. -/
theorem middleRight_natural :
    sourceMap f j j le_rfl g hg ≫ middleRight f' j =
      middleRight f j ≫ sourceMap f j (lastJoint U) (Fin.le_last j.val) g hg := by
  letI : Mono (rightInclusion f' j) := by
    unfold rightInclusion sourceInclusion
    infer_instance
  apply (cancel_mono (rightInclusion f' j)).mp
  simp only [Category.assoc, middleRight_fac, middleRight_fac_assoc, sourceMap_fac]

end Naturality

end

end DaggerModels.PartII.JTTargetIntervalGluing
