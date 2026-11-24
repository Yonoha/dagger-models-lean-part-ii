import DaggerModelsPartII.JTGraphInterpolatedTransport
import DaggerModelsPartII.JTGraphInterpolatedOverOriginal

/-! The decorated and native collapse operators under original target transport. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphInterpolatedTargetOperators

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphLiftTransport
open JTGraphInterpolatedOverOriginal
open JTGraphInterpolatedCollapseOriginal (indexCollapse indexCollapse_operator timeCollapse)
open JTGraphInterpolatedTransport (indexArrow indexArrow_projection)
open JTNecklaceEndpointCylinder (under)
open JTCommaGraphPredecessor (augmentationCode)
open JTTargetCommaPullback (toPullback)
open BoundaryNecklaceComma (necklaceUnder)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {U V : TargetComma Q} {S : NecklaceCode} {n : SimplexCategory}
variable (c : S ⟶ U.left.fiber.left)
variable (D : Fin (n.len + 1) → GraphLift U.left S)
variable (hD : ∀ i, (D i).collapse = c)
variable (a : U ⟶ V)

private abbrev transported := fun i ↦ (D i).transport a.left

include hD in
/-- Each transported lift uses the composite native collapse. -/
theorem transported_collapse (i : Fin (n.len + 1)) :
    (transported D a i).collapse = c ≫ a.left.fiber.left :=
  congrArg (fun f ↦ f ≫ a.left.fiber.left) (hD i)

/-- The decorated operator of the original transport commutes with the collapse. -/
theorem indexCollapse_transport :
    indexArrow c D hD a ≫ indexCollapse (c ≫ a.left.fiber.left) (transported D a)
        (transported_collapse c D hD a) =
      indexCollapse c D hD ≫ ((toPullback W x y Q).map a).base := by
  let L := projection (W := W) (x := x) (y := y)
  have h : L.map (indexArrow c D hD a ≫
      indexCollapse (c ≫ a.left.fiber.left) (transported D a) (transported_collapse c D hD a)) =
        L.map (indexCollapse c D hD ≫ ((toPullback W x y Q).map a).base) := by
    rw [Functor.map_comp, Functor.map_comp, indexArrow_projection,
      indexCollapse_operator, indexCollapse_operator]
    change (𝟙 S ≫ ((c ≫ a.left.fiber.left) ≫ augmentationCode V.left),
          degreeOperator a.left ≫ 𝟙 (degree V.left)) =
      ((c ≫ augmentationCode U.left) ≫ nativeOperator a.left,
        𝟙 (degree U.left) ≫ degreeOperator a.left)
    have hh := (D 0).horizontal_transport a.left
    change ((D 0).collapse ≫ a.left.fiber.left) ≫ augmentationCode V.left =
      ((D 0).collapse ≫ augmentationCode U.left) ≫ nativeOperator a.left at hh
    rw [hD 0] at hh
    change (c ≫ a.left.fiber.left) ≫ augmentationCode V.left =
      (c ≫ augmentationCode U.left) ≫ nativeOperator a.left at hh
    exact Prod.ext ((Category.id_comp _).trans hh)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  exact congrArg (fun f ↦ f.op) h

/-- The native time collapse is compatible with the original target arrow. -/
theorem timeCollapse_transport :
    (𝟙 ((under S).obj n)) ≫ timeCollapse (n := n) (c ≫ a.left.fiber.left) =
      timeCollapse (n := n) c ≫ necklaceUnder.map ((toPullback W x y Q).map a).fiber.left := by
  rw [Category.id_comp]
  apply Under.UnderMorphism.ext
  change NecklaceCylinderAugmentation.augmentation S n ≫ (c ≫ a.left.fiber.left).map =
    (NecklaceCylinderAugmentation.augmentation S n ≫ c.map) ≫ a.left.fiber.left.map
  exact (Category.assoc _ _ _).symm

end

end DaggerModels.PartII.JTGraphInterpolatedTargetOperators
