import DaggerModelsPartII.JTJointRelativeParameters
import DaggerModelsPartII.JTNativeTargetKanWeak
import DaggerModelsPartII.KanLeftProper
import DaggerModelsPartII.TotalElementsWeakComparison
import SSetProductGeometric

/-! Collapse the complete inverse image of a fixed target joint, naturally over that target. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra
open DaggerChosenRigidificationNecklace DaggerSSetGluing
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTJointIntervalQuotient

open JTTargetJointMarks (Joint)
open JTTargetIntervalOverMapping (whole left right overlap overlapToLeft overlapToRight
  leftToWhole rightToWhole over_isPushout)
open JTTargetIntervalGluing (middleInclusion middlePoint middlePB)
open JTTargetIntervalPullback (sourceInterval)

noncomputable section

variable (U : NecklaceCode) (j : Joint U)

private abbrev Slice := Over (U.toSSet : SSet.{0})

/-- The original joint point, over the same fixed target. -/
def joint : Over U ⥤ Slice U :=
  (Functor.const (Over U)).obj (Over.mk (NecklaceCode.pointAt U (ULift.up j.val)))

/-- Collapse precisely the full interval over the joint to that point. -/
def overlapToJoint : overlap U j ⟶ joint U j where
  app P := Over.homMk (middlePoint P.hom j) (middlePB P.hom j).w.symm
  naturality a b g := by
    apply Over.OverMorphism.ext
    exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The full inverse image of the joint includes naturally into the whole source. -/
abbrev overlapToWhole := overlapToLeft U j ≫ leftToWhole U j

theorem overlapToWhole_right :
    overlapToWhole U j = overlapToRight U j ≫ rightToWhole U j := by
  apply NatTrans.ext
  funext P
  exact (over_isPushout U j P).w

/-- The left interval after collapsing its common subinterval. -/
def leftQuotient : Over U ⥤ Slice U :=
  pushout (overlapToLeft U j) (overlapToJoint U j)

/-- The right interval after collapsing its common subinterval. -/
def rightQuotient : Over U ⥤ Slice U :=
  pushout (overlapToRight U j) (overlapToJoint U j)

/-- The whole original source after collapsing the complete common interval. -/
def wholeQuotient : Over U ⥤ Slice U :=
  pushout (overlapToWhole U j) (overlapToJoint U j)

abbrev leftCollapse : left U j ⟶ leftQuotient U j :=
  pushout.inl (overlapToLeft U j) (overlapToJoint U j)

abbrev rightCollapse : right U j ⟶ rightQuotient U j :=
  pushout.inl (overlapToRight U j) (overlapToJoint U j)

abbrev wholeCollapse : whole U ⟶ wholeQuotient U j :=
  pushout.inl (overlapToWhole U j) (overlapToJoint U j)

abbrev jointToLeft : joint U j ⟶ leftQuotient U j :=
  pushout.inr (overlapToLeft U j) (overlapToJoint U j)

abbrev jointToRight : joint U j ⟶ rightQuotient U j :=
  pushout.inr (overlapToRight U j) (overlapToJoint U j)

abbrev jointToWhole : joint U j ⟶ wholeQuotient U j :=
  pushout.inr (overlapToWhole U j) (overlapToJoint U j)

theorem whole_isPushout :
    IsPushout (overlapToWhole U j) (overlapToJoint U j)
      (wholeCollapse U j) (jointToWhole U j) :=
  IsPushout.of_hasPushout _ _

private theorem original_isPushout :
    IsPushout (overlapToLeft U j) (overlapToRight U j) (leftToWhole U j) (rightToWhole U j) := by
  refine ⟨⟨overlapToWhole_right U j⟩,
    ⟨evaluationJointlyReflectsColimits _ (fun P ↦ ?_)⟩⟩
  exact (PushoutCocone.isColimitMapCoconeEquiv _ _).2 (over_isPushout U j P).isColimit

/-- The collapsed left side maps to the collapsed whole over the original target. -/
def leftLeg : leftQuotient U j ⟶ wholeQuotient U j :=
  pushout.desc (leftToWhole U j ≫ wholeCollapse U j) (jointToWhole U j)
    (by rw [← Category.assoc]; exact (whole_isPushout U j).w)

/-- The collapsed right side maps to the collapsed whole over the original target. -/
def rightLeg : rightQuotient U j ⟶ wholeQuotient U j :=
  pushout.desc (rightToWhole U j ≫ wholeCollapse U j) (jointToWhole U j)
    (by rw [← Category.assoc, ← overlapToWhole_right]; exact (whole_isPushout U j).w)

@[reassoc]
theorem leftCollapse_leg :
    leftCollapse U j ≫ leftLeg U j = leftToWhole U j ≫ wholeCollapse U j :=
  pushout.inl_desc _ _ _

@[reassoc]
theorem rightCollapse_leg :
    rightCollapse U j ≫ rightLeg U j = rightToWhole U j ≫ wholeCollapse U j :=
  pushout.inl_desc _ _ _

@[reassoc]
theorem jointToLeft_leg : jointToLeft U j ≫ leftLeg U j = jointToWhole U j :=
  pushout.inr_desc _ _ _

@[reassoc]
theorem jointToRight_leg : jointToRight U j ≫ rightLeg U j = jointToWhole U j :=
  pushout.inr_desc _ _ _

/-- After contraction, the whole source is the gluing of the two contracted sides at the point. -/
theorem quotients_isPushout :
    IsPushout (jointToLeft U j) (jointToRight U j) (leftLeg U j) (rightLeg U j) := by
  have hL : IsPushout (overlapToLeft U j) (overlapToJoint U j)
      (leftCollapse U j) (jointToLeft U j) := IsPushout.of_hasPushout _ _
  have hR : IsPushout (overlapToRight U j) (overlapToJoint U j)
      (rightCollapse U j) (jointToRight U j) := IsPushout.of_hasPushout _ _
  have hw := whole_isPushout U j
  rw [← jointToLeft_leg U j] at hw
  have h₂ : IsPushout (leftToWhole U j) (leftCollapse U j) (wholeCollapse U j) (leftLeg U j) :=
    hw.of_left (leftCollapse_leg U j).symm hL
  have h := (original_isPushout U j).flip.paste_vert h₂
  rw [hL.w, ← rightCollapse_leg] at h
  exact (h.of_top ((jointToRight_leg U j).trans (jointToLeft_leg U j).symm) hR).flip


open DaggerOriginalProductGadget (pointMap pointIsTerminal)

private theorem collapse_app_weak (P : Over U) {B T : Over U ⥤ Slice U}
    {a : overlap U j ⟶ B} {l : B ⟶ T} {r : joint U j ⟶ T}
    (sq : IsPushout a (overlapToJoint U j) l r) (ha : Mono (a.app P).left) :
    WeakEquivalence (l.app P).left := by
  let E := (evaluation (Over U) (Slice U)).obj P ⋙ Over.forget U.toSSet
  have hs := sq.map E
  let C := (sourceInterval P.hom j j le_rfl).toSSet
  let d : C ⟶ Δ[0] := middlePoint P.hom j
  letI : WeakEquivalence (pointMap C) :=
    (weakEquivalence_iff_GW _).mpr (JTNativeTargetKanWeak.point_GW _)
  let e := SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso pointIsTerminal
  letI : WeakEquivalence (pointMap (Δ[0] : SSet.{0})) := by
    rw [← pointIsTerminal.hom_ext e.hom (pointMap _)]
    infer_instance
  have hweak : WeakEquivalence d :=
    weakEquivalence_of_postcomp_of_fac (pointIsTerminal.hom_ext (d ≫ pointMap _) (pointMap C))
  letI : Mono (E.map a) := ha
  haveI : Cofibration (E.map a) :=
    (SSet.modelCategoryQuillen.cofibration_iff _).mpr inferInstance
  exact (weakEquivalence_iff _).mpr (kanLeftProper hs ((cofibration_iff _).mp inferInstance)
    ((weakEquivalence_iff _).mp hweak))

private theorem middleInclusion_mono (P : Over U) : Mono (middleInclusion P.hom j) := by
  unfold middleInclusion JTTargetIntervalPullback.sourceInclusion
  infer_instance

/-- Collapsing the full preimage over the joint is Kan weak at every original source. -/
theorem wholeCollapse_app_weak (P : Over U) :
    WeakEquivalence ((wholeCollapse U j).app P).left := by
  apply collapse_app_weak U j P (whole_isPushout U j)
  change Mono (JTTargetIntervalGluing.middleLeft P.hom j ≫
    JTTargetIntervalGluing.leftInclusion P.hom j)
  rw [JTTargetIntervalGluing.middleLeft_fac]
  exact middleInclusion_mono U j P

/-- The same full interval collapse is Kan weak on the left inverse image. -/
theorem leftCollapse_app_weak (P : Over U) :
    WeakEquivalence ((leftCollapse U j).app P).left := by
  haveI := middleInclusion_mono U j P
  apply collapse_app_weak U j P (IsPushout.of_hasPushout (overlapToLeft U j) (overlapToJoint U j))
  exact mono_of_mono_fac (JTTargetIntervalGluing.middleLeft_fac P.hom j)

/-- The same full interval collapse is Kan weak on the right inverse image. -/
theorem rightCollapse_app_weak (P : Over U) :
    WeakEquivalence ((rightCollapse U j).app P).left := by
  haveI := middleInclusion_mono U j P
  apply collapse_app_weak U j P (IsPushout.of_hasPushout (overlapToRight U j) (overlapToJoint U j))
  exact mono_of_mono_fac (JTTargetIntervalGluing.middleRight_fac P.hom j)

section Time

open JTJointRelativeParameters (withTime withTimeMap withTimeMap_app)
open JTDecoratedIntervalDiagram (parameterize parameterizeMap parameterize_isPushout)

variable {X : SSet.{0}} (q : U.toSSet ⟶ X)
variable {I : Type} [SmallCategory I] (K : SimplexCategory ⥤ SSet.{0})
variable (time : I ⥤ SimplexCategory) (D : I ⥤ Over U)

private abbrev framedMap {V V' : Over U ⥤ Slice U} (a : V ⟶ V') :=
  parameterizeMap q K time (Functor.whiskerLeft D a)

private theorem frame_isPushout {A B C E : Over U ⥤ Slice U}
    {f : A ⟶ B} {g : A ⟶ C} {l : B ⟶ E} {r : C ⟶ E} (sq : IsPushout f g l r) :
    IsPushout (framedMap U q K time D f) (framedMap U q K time D g)
      (framedMap U q K time D l) (framedMap U q K time D r) :=
  parameterize_isPushout q K time (fun a ↦
    sq.map ((evaluation (Over U) (Slice U)).obj (D.obj a)))

/-- The full collapse is still a pushout in the original slice with variable time. -/
theorem timedOver_isPushout :
    IsPushout (framedMap U q K time D (overlapToWhole U j))
      (framedMap U q K time D (overlapToJoint U j))
      (framedMap U q K time D (wholeCollapse U j))
      (framedMap U q K time D (jointToWhole U j)) :=
  frame_isPushout U q K time D (whole_isPushout U j)

/-- The contracted sides still glue at the joint with the full time, over the same target. -/
theorem timedOver_quotients_isPushout :
    IsPushout (framedMap U q K time D (jointToLeft U j))
      (framedMap U q K time D (jointToRight U j))
      (framedMap U q K time D (leftLeg U j))
      (framedMap U q K time D (rightLeg U j)) :=
  frame_isPushout U q K time D (quotients_isPushout U j)

/-- The full collapse is a pushout on the underlying simplicial diagrams. -/
theorem timed_isPushout :
    IsPushout (withTimeMap q K time D (overlapToWhole U j))
      (withTimeMap q K time D (overlapToJoint U j))
      (withTimeMap q K time D (wholeCollapse U j))
      (withTimeMap q K time D (jointToWhole U j)) :=
  (timedOver_isPushout U j q K time D).map
    ((Functor.whiskeringRight I (Over X) SSet.{0}).obj (Over.forget X))

/-- The quotient comparison stays Kan weak on the full product with the time simplicial set. -/
theorem timed_app_weak (a : I) :
    WeakEquivalence ((withTimeMap q K time D (wholeCollapse U j)).app a) := by
  rw [withTimeMap_app]
  exact (weakEquivalence_iff_GW _).mpr (DaggerSSetProductGeometric.tensorMap_geometric _ _
    ((weakEquivalence_iff_GW _).mp (wholeCollapse_app_weak U j (D.obj a)))
    (DaggerSSetProductGeometric.identity_geometric _))

/-- The collapse gives a nerve weak equivalence on the total category of timed simplices. -/
theorem timed_total_weak :
    WeakEquivalence (nerveMap (TotalElementsWeakComparison.totalMap
      (withTimeMap q K time D (wholeCollapse U j)))) :=
  TotalElementsWeakComparison.totalMap_weak _ (timed_app_weak U j q K time D)

variable {Z : I ⥤ SSet.{0}}
variable (s : withTime q K time D (whole U) ⟶ Z)
variable (trace : withTime q K time D (joint U j) ⟶ Z)
variable (h : withTimeMap q K time D (overlapToWhole U j) ≫ s =
  withTimeMap q K time D (overlapToJoint U j) ≫ trace)

/-- A full parameter agreeing with a time-dependent trace on the interval descends naturally. -/
def descend : withTime q K time D (wholeQuotient U j) ⟶ Z :=
  (timed_isPushout U j q K time D).desc s trace h

@[reassoc]
theorem descend_whole :
    withTimeMap q K time D (wholeCollapse U j) ≫ descend U j q K time D s trace h = s :=
  (timed_isPushout U j q K time D).inl_desc s trace h

@[reassoc]
theorem descend_joint :
    withTimeMap q K time D (jointToWhole U j) ≫ descend U j q K time D s trace h = trace :=
  (timed_isPushout U j q K time D).inr_desc s trace h

end Time

end
end DaggerModels.PartII.JTJointIntervalQuotient
