import DaggerModelsPartII.JTGraphBeadBoundaryReflection
import DaggerModelsPartII.JTGraphFactoredComparison
import DaggerModelsPartII.JTNativeOuterCollapse

/-!
# Common graph comparisons after removing constant outer necklaces
-/

set_option autoImplicit false
set_option maxHeartbeats 150000

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTGraphOuterCollapseComparison

open JTProjectiveOrderedFiberComparison (row)
open JTGraphLiftTransport
open JTGraphRestrictionRaw (predecessor)
open JTGraphFactoredPresentation (TargetComma Traversal)
open JTGraphBeadBoundaryReflection
open JTGraphFactoredComparison (ReflectsGraphEquality)
open JTCommaGraphPredecessor (augmentationCode)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {U : TargetComma Q} {L T R : NecklaceCode}

private abbrev S := wedge L (wedge T R)
private abbrev g (L T R : NecklaceCode) := NecklaceCode.collapse.{0} L T R
private abbrev middle (L T R : NecklaceCode) := tripleRightU.{0} L T R

/-- The left and right pieces are constant at the two ends of the middle piece. -/
def ConstantOuterPieces {X : SSet.{0}} (u : (S (L := L) (T := T) (R := R)).toSSet ⟶ X) :
    Prop :=
  (tripleRightT L T R ≫ u =
    outerTerminal L ≫ pointAt T (ULift.up 0) ≫ (middle L T R ≫ u)) ∧
  (tripleRightV L T R ≫ u =
    outerTerminal R ≫ pointAt T (ULift.up (Fin.last T.len)) ≫ (middle L T R ≫ u))

private theorem constantOuter_postcompose {X Y : SSet.{0}}
    (u : (S (L := L) (T := T) (R := R)).toSSet ⟶ X) (p : X ⟶ Y)
    (h : ConstantOuterPieces u) : ConstantOuterPieces (u ≫ p) := by
  constructor
  · simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ p) h.1
  · simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ p) h.2

private theorem constantOuter_of_mono_postcompose {X Y : SSet.{0}}
    (u : (S (L := L) (T := T) (R := R)).toSSet ⟶ X) (p : X ⟶ Y) [Mono p]
    (h : ConstantOuterPieces (u ≫ p)) : ConstantOuterPieces u := by
  constructor
  · apply (cancel_mono p).mp
    simpa only [Category.assoc] using h.1
  · apply (cancel_mono p).mp
    simpa only [Category.assoc] using h.2

variable (c : S (L := L) (T := T) (R := R) ⟶ U.left.fiber.left)

private abbrev cylinderMap := c.map ≫ U.left.fiber.hom.right
private abbrev targetMap := c ≫ U.hom.hom

variable (hv : ConstantOuterPieces (cylinderMap c))
  (hr : ConstantOuterPieces (targetMap c).map)

include hv

/-- For a monic target traversal, constancy in the cylinder forces constancy
of the native target map on both discarded pieces. -/
theorem target_outer_of_mono [Mono Q.map] : ConstantOuterPieces (targetMap c).map := by
  let d := ((DecoratedCylinderNecklacePresentation.underCocone W x y).app U.left.base).right
  have hu : U.hom.hom.map ≫ Q.map = U.left.fiber.hom.right ≫ d := U.hom.w
  have h : (targetMap c).map ≫ Q.map = cylinderMap c ≫ d := by
    change (c.map ≫ U.hom.hom.map) ≫ Q.map = (c.map ≫ U.left.fiber.hom.right) ≫ d
    rw [Category.assoc, hu, Category.assoc]
  apply constantOuter_of_mono_postcompose (targetMap c).map Q.map
  exact h.symm ▸ constantOuter_postcompose (cylinderMap c) d hv

private theorem cylinder_factor :
    (g L T R).map ≫ (middle L T R ≫ cylinderMap c) = cylinderMap c :=
  (factors_of_outer_constants L T R (cylinderMap c) hv.1 hv.2).symm

/-- Restrict the original reduced-cylinder traversal to the retained middle necklace. -/
def middleTraversal : Traversal U T :=
  Under.homMk (middle L T R ≫ cylinderMap c) (by
    let B := JTNecklaceEndpointCylinder.endpointInclusion
    let d := U.left.fiber.hom
    change B T ≫ (middle L T R ≫ cylinderMap c) =
      ((DecoratedCylinderNecklacePresentation.underDiagram W x y).obj U.left.base).hom
    calc
      _ = (B (S (L := L) (T := T) (R := R)) ≫ (g L T R).map) ≫
          (middle L T R ≫ cylinderMap c) :=
        congrArg (fun u ↦ u ≫ (middle L T R ≫ cylinderMap c))
          (JTNecklaceEndpointCylinder.endpointInclusion_natural (g L T R)).symm
      _ = B (S (L := L) (T := T) (R := R)) ≫ cylinderMap c :=
        (Category.assoc _ _ _).trans
          (congrArg (fun u ↦ B (S (L := L) (T := T) (R := R)) ≫ u) (cylinder_factor c hv))
      _ = _ := by
        change B (S (L := L) (T := T) (R := R)) ≫ c.map ≫ d.right = _
        rw [← Category.assoc, JTNecklaceEndpointCylinder.endpointInclusion_natural]
        exact Under.w d)

/-- The middle necklace with its exact native map into the same raw target. -/
def middleObject : TargetComma Q :=
  JTGraphFactoredPresentation.object U c (g L T R) (middleTraversal c hv)
    (factorNative L T R Q.code (targetMap c) hr.1 hr.2)
    (cylinder_factor c hv) (collapse_factorNative L T R Q.code (targetMap c) hr.1 hr.2)

/-- Every lift of the original collapse compares to one graph on the middle
necklace if both outer pieces are constant in the cylinder and in the
native target code, and the retained horizontal map reflects the boundary. -/
theorem exists_common
    (hf : ReflectsGraphEquality (g L T R) (augmentationCode (middleObject c hv hr).left)
      (degree U.left)) :
    ∃ E : GraphLift (middleObject c hv hr).left T, E.collapse = 𝟙 _ ∧
      ∀ D : GraphLift U.left (S (L := L) (T := T) (R := R)), D.collapse = c →
        Nonempty (predecessor (U := U) D ⟶ predecessor (U := middleObject c hv hr) E) :=
  JTGraphFactoredComparison.exists_common c (g L T R) (middleTraversal c hv)
    (factorNative L T R Q.code (targetMap c) hr.1 hr.2)
    (cylinder_factor c hv) (collapse_factorNative L T R Q.code (targetMap c) hr.1 hr.2)
    hf

/-- It suffices to check boundary reflection on the full source bead generators. -/
theorem middle_reflectsGraphEquality_of_beads
    (hf : ReflectsBeadBoundary (g L T R) (augmentationCode (middleObject c hv hr).left)) :
    ReflectsGraphEquality (g L T R) (augmentationCode (middleObject c hv hr).left)
      (degree U.left) :=
  graph_eq_of_reflectsBeadBoundary (g L T R) _ hf (degree U.left)

end

end DaggerModels.PartII.JTGraphOuterCollapseComparison
