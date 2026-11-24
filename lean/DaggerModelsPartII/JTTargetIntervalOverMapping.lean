import DaggerModelsPartII.JTTargetIntervalGluing
import DaggerModelsPartII.JTOverParametrizedMapping

/-!
# The native interval gluing over the entire fixed target

The source interval pushout lifts to the slice over the full target
necklace. Its maps are natural along the native over-target arrows.
The outer ordered endpoints are carried by the corresponding side.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTTargetIntervalOverMapping

open NecklaceCode JTTargetJointMarks JTTargetIntervalPullback
open JTTargetIntervalGluing (leftInclusion rightInclusion middleLeft middleRight
  middleLeft_fac middleRight_fac middleLeft_natural middleRight_natural)
open DaggerOriginalProductGadget (intervalPoint_first intervalPoint_last)

noncomputable section

local instance : SmallCategory NecklaceCode := NecklaceCode.category

variable (U : NecklaceCode)

/-- The actual native map, regarded as a simplicial-set map over the target. -/
abbrev whole : Over U ⥤ Over U.toSSet := Over.post NecklaceCode.simplicialFunctor

private def intervalArrow (a b : Joint U) (hab : a.val ≤ b.val)
    {P P' : Over U} (g : P ⟶ P') :
    Over.mk (sourceInclusion P.hom a b hab ≫ P.hom.map) ⟶
      Over.mk (sourceInclusion P'.hom a b hab ≫ P'.hom.map) :=
  Over.homMk (sourceMap P.hom a b hab g.left (Over.w g)) (by
    change sourceMap P.hom a b hab g.left (Over.w g) ≫
        (sourceInclusion P'.hom a b hab ≫ P'.hom.map) =
      sourceInclusion P.hom a b hab ≫ P.hom.map
    have hg : g.left.map ≫ P'.hom.map = P.hom.map :=
      congrArg (fun h : P.left ⟶ U ↦ h.map) (Over.w g)
    rw [← Category.assoc, sourceMap_fac, Category.assoc, hg])

/-- Restrict an arbitrary native map to the preimage of a fixed target interval. -/
def interval (a b : Joint U) (hab : a.val ≤ b.val) : Over U ⥤ Over U.toSSet where
  obj P := Over.mk (sourceInclusion P.hom a b hab ≫ P.hom.map)
  map g := intervalArrow U a b hab g
  map_id P := by
    apply Over.OverMorphism.ext
    exact sourceMap_id P.hom a b hab
  map_comp {_ _ _} g h := by
    apply Over.OverMorphism.ext
    exact sourceMap_comp _ a b hab g.left (Over.w g) h.left (Over.w h)

/-- All interval inclusions are natural over the literal native target. -/
def inclusion (a b : Joint U) (hab : a.val ≤ b.val) :
    interval U a b hab ⟶ whole U where
  app P := Over.homMk (sourceInclusion P.hom a b hab) rfl
  naturality {_ _} g := by
    apply Over.OverMorphism.ext
    exact sourceMap_fac _ a b hab g.left (Over.w g)

private abbrev firstJoint : Joint U := ⟨0, U.first_mem⟩
private abbrev lastJoint : Joint U := ⟨Fin.last U.len, U.last_mem⟩

variable (j : Joint U)

/-- The left, right, and overlap functors retain the native target throughout. -/
abbrev left := interval U (firstJoint U) j (Fin.zero_le j.val)
abbrev right := interval U j (lastJoint U) (Fin.le_last j.val)
abbrev overlap := interval U j j le_rfl

abbrev leftToWhole := inclusion U (firstJoint U) j (Fin.zero_le j.val)
abbrev rightToWhole := inclusion U j (lastJoint U) (Fin.le_last j.val)

/-- The full common interval includes naturally into the left interval. -/
def overlapToLeft : overlap U j ⟶ left U j where
  app P := Over.homMk (middleLeft P.hom j) (by
    change middleLeft P.hom j ≫ (leftInclusion P.hom j ≫ P.hom.map) =
      sourceInclusion P.hom j j le_rfl ≫ P.hom.map
    rw [← Category.assoc, middleLeft_fac])
  naturality {_ _} g := by
    apply Over.OverMorphism.ext
    exact middleLeft_natural _ j g.left (Over.w g)

/-- The full common interval includes naturally into the right interval. -/
def overlapToRight : overlap U j ⟶ right U j where
  app P := Over.homMk (middleRight P.hom j) (by
    change middleRight P.hom j ≫ (rightInclusion P.hom j ≫ P.hom.map) =
      sourceInclusion P.hom j j le_rfl ≫ P.hom.map
    rw [← Category.assoc, middleRight_fac])
  naturality {_ _} g := by
    apply Over.OverMorphism.ext
    exact middleRight_natural _ j g.left (Over.w g)

/-- The entire source is the pushout in the slice over the original target. -/
theorem over_isPushout (P : Over U) :
    IsPushout ((overlapToLeft U j).app P) ((overlapToRight U j).app P)
      ((leftToWhole U j).app P) ((rightToWhole U j).app P) := by
  apply IsPushout.of_map_of_faithful (Over.forget U.toSSet)
  exact JTTargetIntervalGluing.isPushout P.hom j

/-- The first endpoint of the left interval is the original first endpoint. -/
theorem left_first (P : Over U) :
    pointAt (sourceInterval P.hom (firstJoint U) j (Fin.zero_le j.val)) (ULift.up 0) ≫
        leftInclusion P.hom j =
      pointAt P.left (ULift.up 0) := by
  have h : (least P.hom (firstJoint U)).val = 0 :=
    le_antisymm ((least_le_iff P.hom (firstJoint U) 0).2
      (le_of_eq (orderMap_first P.hom).symm)) (Fin.zero_le _)
  calc
    _ = pointAt P.left (ULift.up (least P.hom (firstJoint U)).val) :=
      intervalPoint_first P.left _ _ _
    _ = _ := congrArg (fun k ↦ pointAt P.left (ULift.up k)) h

/-- The last endpoint of the right interval is the original last endpoint. -/
theorem right_last (P : Over U) :
    pointAt (sourceInterval P.hom j (lastJoint U) (Fin.le_last j.val))
        (ULift.up (Fin.last (sourceInterval P.hom j (lastJoint U) (Fin.le_last j.val)).len)) ≫
      rightInclusion P.hom j = pointAt P.left (ULift.up (Fin.last P.left.len)) := by
  have h : (greatest P.hom (lastJoint U)).val = Fin.last P.left.len :=
    le_antisymm (Fin.le_last _) ((le_greatest_iff P.hom (lastJoint U) (Fin.last P.left.len)).2
      (orderMap_last P.hom).le)
  calc
    _ = pointAt P.left (ULift.up (greatest P.hom (lastJoint U)).val) :=
      intervalPoint_last P.left _ _ _
    _ = _ := congrArg (fun k ↦ pointAt P.left (ULift.up k)) h

/-- The actual interval restrictions form a pullback of parametrized maps over the target. -/
theorem mapping_isPullback (K : SimplexCategory ⥤ SSet.{0}) (P : Over U) (A : Over U.toSSet) :
    IsPullback (JTOverParametrizedMapping.precomp K U.toSSet ((leftToWhole U j).app P) A)
      (JTOverParametrizedMapping.precomp K U.toSSet ((rightToWhole U j).app P) A)
      (JTOverParametrizedMapping.precomp K U.toSSet ((overlapToLeft U j).app P) A)
      (JTOverParametrizedMapping.precomp K U.toSSet ((overlapToRight U j).app P) A) :=
  JTOverParametrizedMapping.mapping_isPullback K U.toSSet (over_isPushout U j P) A

end

end DaggerModels.PartII.JTTargetIntervalOverMapping
