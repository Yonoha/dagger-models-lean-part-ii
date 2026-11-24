import DaggerModelsPartII.JTGraphInterpolatedOverOriginal
import DaggerModelsPartII.JTBoundaryNecklaceConeReindex

/-!
# Time restriction of the interpolation over an original comma object
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphInterpolatedOverTime

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphLiftTransport
open JTGraphInterpolatedComparison (comparisonFunctor_reindex decorated_reindex)
open JTGraphInterpolatedOverOriginal
open JTGraphInterpolatedCollapseOriginal
open JTGraphInterpolatedRaw (index toDecorated whole_raw)
open JTCommaGraphPredecessor (augmentationCode)
open JTNecklaceEndpointCylinder (under value cylinder)
open NecklaceCylinderAugmentation (augmentation augmentation_parameter_natural)
open JTTargetCommaPullback (diagram toPullback equivalence)
open JTBoundaryNecklaceConeReindex (cone_reindex mapCone_reindex overLift_reindex)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {U : TargetComma Q} {S : NecklaceCode} {m n : SimplexCategory}
variable (c : S ⟶ U.left.fiber.left)
variable (D : Fin (n.len + 1) → GraphLift U.left S)
variable (hD : ∀ i, (D i).collapse = c)
variable (j : m ⟶ n)

private abbrev reindexed := fun i ↦ D (j.toOrderHom i)

/-- The decorated operator to the original object is independent of time. -/
theorem indexCollapse_reindex :
    indexCollapse c D hD = indexCollapse c (reindexed D j) (fun i ↦ hD (j.toOrderHom i)) := by
  have h : (projection (W := W) (x := x) (y := y)).map (indexCollapse c D hD) =
      (projection (W := W) (x := x) (y := y)).map
        (indexCollapse c (reindexed D j) (fun i ↦ hD (j.toOrderHom i))) := by
    rw [indexCollapse_operator, indexCollapse_operator]
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  exact congrArg (fun f ↦ f.op) h

/-- The collapse on native necklaces commutes with time restriction. -/
theorem timeCollapse_reindex :
    (under S).map j ≫ timeCollapse (n := n) c = timeCollapse (n := m) c := by
  apply Under.UnderMorphism.ext
  change (value S).map j ≫ augmentation S n ≫ c.map = augmentation S m ≫ c.map
  rw [← Category.assoc, augmentation_parameter_natural]

include hD in
private theorem parameter_comm (i : Fin (n.len + 1)) :
    lift (c ≫ augmentationCode U.left).map (D i).parameter ≫
        (cylinder (code U.left)).app (degree U.left) = c.map ≫ U.left.fiber.hom.right := by
  have h := (D i).comm
  rw [hD i] at h
  exact h

/-- The original cylinder lift commutes with time restriction. -/
theorem pullbackLift_reindex :
    (under S).map j ≫ pullbackLift c D hD =
      pullbackLift c (reindexed D j) (fun i ↦ hD (j.toOrderHom i)) :=
  JTCylinderOverTargetReindex.lift_reindex W x y Q (index U c) S m n j
    (toDecorated U c (fun i ↦ (D (j.toOrderHom i)).parameter))
    (toDecorated U c (fun i ↦ (D i).parameter)) (c ≫ U.hom.hom)
    (whole_raw U c _ (fun i ↦ parameter_comm c D hD (j.toOrderHom i)))
    (whole_raw U c _ (parameter_comm c D hD))
    (decorated_reindex c D j)

/-- Restriction preserves the comparison to the original comma object. -/
theorem comparisonToOriginal_reindex :
    Functor.whiskerLeft (CostructuredArrow.map ((under S).map j))
        (comparisonToOriginal c D hD) =
      eqToHom (comparisonFunctor_reindex c D hD j) ≫
        comparisonToOriginal c (reindexed D j) (fun i ↦ hD (j.toOrderHom i)) := by
  have hP := pullbackLift_reindex c D hD j
  have hB := timeCollapse_reindex c j
  have h := cone_reindex (diagram W x y Q) ((toPullback W x y Q).obj U)
    (pullbackLift c (reindexed D j) (fun i ↦ hD (j.toOrderHom i))) (pullbackLift c D hD)
    (indexCollapse c (reindexed D j) (fun i ↦ hD (j.toOrderHom i))) (indexCollapse c D hD)
    (timeCollapse (n := m) c) (timeCollapse (n := n) c)
    ((under S).map j) hP hB (indexCollapse_reindex c D hD j)
    (pullback_collapse c (reindexed D j) (fun i ↦ hD (j.toOrderHom i))) (pullback_collapse c D hD)
  unfold comparisonToOriginal
  exact mapCone_reindex (CostructuredArrow.map ((under S).map j))
    (presentationCone c D hD)
    (presentationCone c (reindexed D j) (fun i ↦ hD (j.toOrderHom i)))
    (JTCylinderOverTargetBaseChangeTime.source_eq (diagram W x y Q)
      (pullbackLift c (reindexed D j) (fun i ↦ hD (j.toOrderHom i)))
      (pullbackLift c D hD) ((under S).map j) hP)
    h (equivalence W x y Q).inverse ((equivalence W x y Q).unitIso.app U).inv

/-- Reindexing gives the same functor into the slice over the original object. -/
theorem overOriginal_reindex :
    CostructuredArrow.map ((under S).map j) ⋙ overOriginal c D hD =
      overOriginal c (reindexed D j) (fun i ↦ hD (j.toOrderHom i)) :=
  overLift_reindex (CostructuredArrow.map ((under S).map j)) _ _
    (comparisonFunctor_reindex c D hD j) (comparisonToOriginal_reindex c D hD j)

end

end DaggerModels.PartII.JTGraphInterpolatedOverTime
