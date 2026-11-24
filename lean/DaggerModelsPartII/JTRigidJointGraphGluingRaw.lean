import DaggerModelsPartII.JTRigidJointGraphGluing
import DaggerModelsPartII.JTFullBoundaryGraphEvaluation

/-! Raw and endpoint-reduced evaluation of the weak pushout cover. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels MonoidalCategory
open MorphismProperty CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTRigidJointGraphGluing

open JTJointRelativeParameters (withTime underlying_isPushout)
open JTJointRelativeGraphFamily (native coefficient leftLeg rightLeg RawOn)
open JTParametrizedTargetFamilies (Family codes)
open JTTargetIntervalOverMapping (left right whole)
open JTTargetJointMarks (Joint)
open JTRigidOverlapDiagram (CommonCover)
open JTRigidJointGraphCover (overlapData coveredLeft coveredRight coveredSides_parameter_agree)
open JTNecklaceEndpointCylinder (cylinder)
open DecoratedCylinderNecklacePresentation (underCocone)

noncomputable section

set_option maxHeartbeats 1600000

private abbrev J := GroupoidSimplex.parameter
private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {I : Type} [SmallCategory I] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : I ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : I ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code)
variable (s : withTime Q.map J time (native F) (left Q.code j) ⟶ coefficient (L := L) ⋙ J)
variable (t : withTime Q.map J time (native F) (right Q.code j) ⟶ coefficient (L := L) ⋙ J)
variable (C : CommonCover (overlapData F j s t))

local instance : ModelCategory (I ⥤ SSet.{0}) := InjectiveKanDiagram.modelCategory I

private abbrev leftSide := coveredLeft F j s t C
private abbrev rightSide := coveredRight F j s t C
private abbrev allSource := withTime Q.map J time (native F) (whole Q.code)
private abbrev splitLeft :=
  factorizationData (cofibrations (I ⥤ SSet.{0})) (trivialFibrations (I ⥤ SSet.{0}))
    (leftSide F j s t C).fromOverlap

private abbrev nativeProjection (p : I) :=
  fst ((codes L).obj p).toSSet (J.obj (time.obj p))

private abbrev rawRealization (p : I) :=
  (cylinder ((codes L).obj p)).app ((coefficient (L := L)).obj p) ≫
    ((underCocone W x y).app (L.obj p)).right

private abbrev originalRaw (p : I) :=
  nativeProjection (L := L) (time := time) p ≫ (F.collapse.app p).map ≫ Q.map

private theorem prefixed_raw (p : I)
    {X Y : SSet.{0}} (e : X ⟶ (allSource F).obj p)
    (s' : X ⟶ J.obj ((coefficient (L := L)).obj p))
    (v : Y ⟶ X) (t' : Y ⟶ J.obj ((coefficient (L := L)).obj p))
    (he : lift (e ≫ nativeProjection (L := L) (time := time) p) s' ≫ rawRealization p =
      e ≫ originalRaw F p)
    (hv : lift (v ≫ e ≫ nativeProjection (L := L) (time := time) p) t' ≫
        (cylinder ((codes L).obj p)).app ((coefficient (L := L)).obj p) =
      v ≫ lift (e ≫ nativeProjection (L := L) (time := time) p) s' ≫
        (cylinder ((codes L).obj p)).app ((coefficient (L := L)).obj p)) :
    lift (v ≫ e ≫ nativeProjection (L := L) (time := time) p) t' ≫ rawRealization p =
      v ≫ e ≫ originalRaw F p := by
  have h := congrArg (· ≫ ((underCocone W x y).app (L.obj p)).right) hv
  simpa only [Category.assoc, he] using h

/-- The actual glued cover retains the exact raw image of the original necklace. -/
theorem assembled_raw (hs : RawOn F (leftLeg F j) s) (ht : RawOn F (rightLeg F j) t)
    (p : I) :
    lift ((projection F j s t C).app p ≫ nativeProjection (L := L) (time := time) p)
        ((parameter F j s t C).app p) ≫ rawRealization p =
      (projection F j s t C).app p ≫ originalRaw F p := by
  let a' := (leftSide F j s t C).fromOverlap
  let b' := (rightSide F j s t C).fromOverlap
  let l := pushout.inl (splitLeft F j s t C).i b'
  let r := pushout.inr (splitLeft F j s t C).i b'
  have hl : l.app p ≫ (projection F j s t C).app p =
      ((splitLeft F j s t C).p ≫ (leftSide F j s t C).projection).app p ≫
        (leftLeg F j).app p :=
    NatTrans.congr_app (JTWeakCoveredPushout.inl_projection
      (underlying_isPushout Q J time (native F) j) a' b' C.projection
      (leftSide F j s t C).projection (rightSide F j s t C).projection
      (leftSide F j s t C).projectsOverlap (rightSide F j s t C).projectsOverlap) p
  have hr : r.app p ≫ (projection F j s t C).app p =
      (rightSide F j s t C).projection.app p ≫ (rightLeg F j).app p :=
    NatTrans.congr_app (JTWeakCoveredPushout.inr_projection
      (underlying_isPushout Q J time (native F) j) a' b' C.projection
      (leftSide F j s t C).projection (rightSide F j s t C).projection
      (leftSide F j s t C).projectsOverlap (rightSide F j s t C).projectsOverlap) p
  have hl' : l.app p ≫ (parameter F j s t C).app p =
      (splitLeft F j s t C).p.app p ≫ (leftSide F j s t C).parameter.app p :=
    NatTrans.congr_app (JTWeakCoveredPushout.inl_parameter a' b'
      (leftSide F j s t C).parameter (rightSide F j s t C).parameter
      (coveredSides_parameter_agree F j s t C)) p
  have hr' : r.app p ≫ (parameter F j s t C).app p =
      (rightSide F j s t C).parameter.app p :=
    NatTrans.congr_app (JTWeakCoveredPushout.inr_parameter a' b'
      (leftSide F j s t C).parameter (rightSide F j s t C).parameter
      (coveredSides_parameter_agree F j s t C)) p
  have hl0 : ((evaluation I SSet.{0}).obj p).map
      (pushout.inl (splitLeft F j s t C).i b') ≫ (projection F j s t C).app p =
      ((splitLeft F j s t C).p ≫ (leftSide F j s t C).projection).app p ≫
        (leftLeg F j).app p := hl
  have hr0 : ((evaluation I SSet.{0}).obj p).map
      (pushout.inr (splitLeft F j s t C).i b') ≫ (projection F j s t C).app p =
      (rightSide F j s t C).projection.app p ≫ (rightLeg F j).app p := hr
  apply ((IsPushout.of_hasPushout (splitLeft F j s t C).i b').map
    ((evaluation I SSet.{0}).obj p)).hom_ext
  · change l.app p ≫ _ = _
    simp only [← Category.assoc, CartesianMonoidalCategory.comp_lift,
      hl, hl0, hl', NatTrans.comp_app]
    have h := prefixed_raw F p _ _ _ _ (hs p) ((leftSide F j s t C).exactGraph p)
    have h' := congrArg ((splitLeft F j s t C).p.app p ≫ ·) h
    simpa only [← Category.assoc, CartesianMonoidalCategory.comp_lift] using h'
  · change r.app p ≫ _ = _
    simp only [← Category.assoc, CartesianMonoidalCategory.comp_lift,
      hr, hr0, hr']
    simpa only [Category.assoc] using
      prefixed_raw F p _ _ _ _ (ht p) ((rightSide F j s t C).exactGraph p)

/-- The glued parameter satisfies the original raw-image predicate. -/
theorem assembled_rawOn (hs : RawOn F (leftLeg F j) s)
    (ht : RawOn F (rightLeg F j) t) :
    RawOn F (projection F j s t C) (parameter F j s t C) := by
  intro p
  exact assembled_raw F j s t C hs ht p

/-- Collapse the full endpoint inverse images and evaluate the glued pushout
in the same fixed-target comma as the two references. -/
def evaluate (hs : RawOn F (leftLeg F j) s) (ht : RawOn F (rightLeg F j) t) :
    BoundaryNecklaceComma.Presentation
      (JTFullBoundaryGraphEvaluation.reduced F (projection F j s t C)) ⥤
        JTGraphFactoredPresentation.TargetComma Q :=
  JTFullBoundaryGraphEvaluation.evaluate F (projection F j s t C) (parameter F j s t C)
    (assembled_rawOn F j s t C hs ht)

end

end DaggerModels.PartII.JTRigidJointGraphGluing
