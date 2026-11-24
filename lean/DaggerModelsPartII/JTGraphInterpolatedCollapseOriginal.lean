import DaggerModelsPartII.JTGraphInterpolatedComparison
import DaggerModelsPartII.JTGraphTransportNaturality

/-!
# Collapse of the interpolated cylinder to the original comma object
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphInterpolatedCollapseOriginal

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphLiftTransport
open JTGraphInterpolatedComparison (Fiber comparisonFunctor)
open JTGraphInterpolatedRaw (index toDecorated whole_raw whole_cylinder_by)
open JTGraphParameterInterpolation (interpolate)
open JTCommaGraphPredecessor (augmentationCode)
open JTNecklaceEndpointCylinder (under cylinder nativeMap value)
open NecklaceCylinderAugmentation (augmentation augmentation_boundary)
open BoundaryNecklaceComma (necklaceUnder)
open DecoratedCylinderNecklacePresentation (underDiagram underCocone)
open JTTargetCommaPullback (diagram targetMap map_fst map_snd toPullback equivalence)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev J := GroupoidSimplex.parameter
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {U : TargetComma Q} {S : NecklaceCode} {n : SimplexCategory}
variable (c : S ⟶ U.left.fiber.left)
variable (D : Fin (n.len + 1) → GraphLift U.left S)
variable (hD : ∀ i, (D i).collapse = c)

include hD in
private theorem parameter_comm (i : Fin (n.len + 1)) :
    lift (c ≫ augmentationCode U.left).map ((D i).parameter) ≫
        (cylinder (code U.left)).app (degree U.left) = c.map ≫ U.left.fiber.hom.right := by
  have h := (D i).comm
  rw [hD i] at h
  exact h

private def reference : GraphLift U.left S := ⟨c, (D 0).parameter, parameter_comm c D hD 0⟩

/-- The original decorated operator to the chosen comma presentation. -/
def indexCollapse : index U c ⟶ U.left.base :=
  (JTGraphTransportNaturality.toComma (reference c D hD)).left.base

theorem indexCollapse_operator :
    (projection (W := W) (x := x) (y := y)).map (indexCollapse c D hD) =
      (c ≫ augmentationCode U.left, 𝟙 (degree U.left)) := rfl

/-- Augmentation of the time cylinder followed by the specified native collapse. -/
def timeCollapse : (under S).obj n ⟶ necklaceUnder.obj U.left.fiber.left :=
  Under.homMk (augmentation S n ≫ c.map) (by
    change (JTNecklaceEndpointCylinder.boundary S).app n ≫ augmentation S n ≫ c.map =
      JTNecklaceEndpointCylinder.endpointInclusion U.left.fiber.left
    rw [← Category.assoc, augmentation_boundary, JTNecklaceEndpointCylinder.endpointInclusion_natural])

private abbrev decorated := toDecorated U c (fun i ↦ (D i).parameter)
/-- The original time-cylinder map into the fixed-target pullback. -/
abbrev pullbackLift :=
  JTCylinderOverTarget.lift W x y Q (index U c) S n (decorated c D)
    (c ≫ U.hom.hom) (whole_raw U c _ (parameter_comm c D hD))

/-- The complete cylinder traversal is compatible with the native collapse
into the original internal necklace. -/
theorem decorated_collapse :
    decorated c D ≫ (underDiagram W x y).map (indexCollapse c D hD) =
      timeCollapse (n := n) c ≫ U.left.fiber.hom := by
  apply Under.UnderMorphism.ext
  change (decorated c D).right ≫
      (nativeMap (c ≫ augmentationCode U.left) (degree U.left) ≫
        (value (code U.left)).map (𝟙 (degree U.left))) =
    (augmentation S n ≫ c.map) ≫ U.left.fiber.hom.right
  rw [(value (code U.left)).map_id, Category.comp_id, Category.assoc]
  exact whole_cylinder_by U c (interpolate (fun i ↦ (D i).parameter))
    (JTGraphParameterFiber.interpolate_fiber (code U.left) (degree U.left) n
      (c ≫ augmentationCode U.left).map (fun i ↦ (D i).parameter)
      (c.map ≫ U.left.fiber.hom.right) (parameter_comm c D hD))

/-- Both projections give the actual comparison with the original comma object. -/
theorem pullback_collapse :
    pullbackLift c D hD ≫ (diagram W x y Q).map (indexCollapse c D hD) =
      timeCollapse (n := n) c ≫ ((toPullback W x y Q).obj U).fiber.hom := by
  change pullbackLift c D hD ≫ (diagram W x y Q).map (indexCollapse c D hD) =
    timeCollapse (n := n) c ≫ JTTargetCommaPullback.lift W x y Q U
  apply pullback.hom_ext (f := (underCocone W x y).app U.left.base) (g := targetMap W x y Q)
  · change (_ ≫ _) ≫ JTTargetCommaPullback.fst W x y Q U.left.base =
      (_ ≫ _) ≫ JTTargetCommaPullback.fst W x y Q U.left.base
    rw [Category.assoc, map_fst, ← Category.assoc, JTCylinderOverTarget.lift_decorated,
      decorated_collapse, Category.assoc, JTTargetCommaPullback.lift_fst]
  · change (_ ≫ _) ≫ JTTargetCommaPullback.snd W x y Q U.left.base =
      (_ ≫ _) ≫ JTTargetCommaPullback.snd W x y Q U.left.base
    rw [Category.assoc, map_snd, JTCylinderOverTarget.lift_native,
      Category.assoc, JTTargetCommaPullback.lift_snd]
    apply Under.UnderMorphism.ext
    change augmentation S n ≫ (c ≫ U.hom.hom).map =
      (augmentation S n ≫ c.map) ≫ U.hom.hom.map
    exact (Category.assoc _ _ _).symm

end

end DaggerModels.PartII.JTGraphInterpolatedCollapseOriginal
