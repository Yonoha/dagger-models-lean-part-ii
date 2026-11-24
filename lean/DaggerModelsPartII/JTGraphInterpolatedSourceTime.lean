import DaggerModelsPartII.JTGraphInterpolatedSourceComparison
import DaggerModelsPartII.JTCylinderOverTargetBaseChangeTime

/-!
# Time restriction of interpolated native source comparisons
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphInterpolatedSourceTime

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphLiftTransport
open JTGraphLiftRestriction (restrict)
open JTGraphInterpolatedComparison (comparisonFunctor comparisonFunctor_reindex decorated_reindex)
open JTGraphInterpolatedSourceComparison
open JTGraphInterpolatedRaw (index toDecorated whole_raw)
open JTNecklaceEndpointCylinder (under cylinder)
open JTCylinderOverTargetBaseChangeTime (reindex_target)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {U : TargetComma Q} {R S : NecklaceCode} {m n : SimplexCategory}

/-- The decorated source operator depends only on the native map and collapse. -/
theorem indexArrow_independent (c : S ⟶ U.left.fiber.left) (g : R ⟶ S)
    (D : Fin (n.len + 1) → GraphLift U.left S) (hD : ∀ i, (D i).collapse = c)
    (D₀ : Fin (m.len + 1) → GraphLift U.left S) (hD₀ : ∀ i, (D₀ i).collapse = c) :
    indexArrow c D hD g = indexArrow c D₀ hD₀ g := by
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  exact congrArg (fun f ↦ f.op)
    ((indexArrow_operator c D hD g).trans (indexArrow_operator c D₀ hD₀ g).symm)

variable (c : S ⟶ U.left.fiber.left)
variable (D : Fin (n.len + 1) → GraphLift U.left S)
variable (hD : ∀ i, (D i).collapse = c)
variable (g : R ⟶ S) (j : m ⟶ n)

private abbrev restricted := fun i ↦ restrict (D i) g
private abbrev reindexed := fun i ↦ D (j.toOrderHom i)

include hD in
private theorem restricted_collapse (i : Fin (n.len + 1)) :
    (restricted D g i).collapse = g ≫ c :=
  congrArg (fun d ↦ g ≫ d) (hD i)

include hD in
private theorem parameter_comm (i : Fin (n.len + 1)) :
    lift (c ≫ JTCommaGraphPredecessor.augmentationCode U.left).map ((D i).parameter) ≫
        (cylinder (code U.left)).app (degree U.left) = c.map ≫ U.left.fiber.hom.right := by
  have h := (D i).comm
  rw [hD i] at h
  exact h

set_option maxHeartbeats 400000 in
/-- Restricting a native source comparison in time gives the comparison of
the restricted graph families, with the canonical endpoint identifications. -/
theorem sourceComparison_reindex :
    Functor.whiskerLeft (CostructuredArrow.map ((under R).map j))
        (sourceComparison c D hD g) ≫
      eqToHom (reindex_target ((under R).map j) ((under S).map j)
        (sourceMap g m) (sourceMap g n) _ _ (sourceMap_time g j).symm
        (comparisonFunctor_reindex c D hD j)) =
    eqToHom (comparisonFunctor_reindex (g ≫ c) (restricted D g)
        (restricted_collapse c D hD g) j) ≫
      sourceComparison c (reindexed D j) (fun i ↦ hD (j.toOrderHom i)) g := by
  let D₀ := reindexed D j
  let hD₀ : ∀ i, (D₀ i).collapse = c := fun i ↦ hD (j.toOrderHom i)
  let C := restricted D g
  let C₀ := restricted D₀ g
  let hC := restricted_collapse c D hD g
  let hC₀ := restricted_collapse c D₀ hD₀ g
  let a := indexArrow c D hD g
  have hDm := decorated_source c D₀ hD₀ g
  change toDecorated U (g ≫ c) (fun i ↦ (C₀ i).parameter) ≫
    (DecoratedCylinderNecklacePresentation.underDiagram W x y).map a =
    sourceMap g m ≫ toDecorated U c (fun i ↦ (D₀ i).parameter) at hDm
  have H := JTCylinderOverTargetBaseChangeTime.compare_reindex W x y Q
    (index U (g ≫ c)) (index U c) R S j
    (toDecorated U (g ≫ c) (fun i ↦ (C₀ i).parameter))
    (toDecorated U (g ≫ c) (fun i ↦ (C i).parameter))
    (toDecorated U c (fun i ↦ (D₀ i).parameter))
    (toDecorated U c (fun i ↦ (D i).parameter))
    ((g ≫ c) ≫ U.hom.hom) (c ≫ U.hom.hom)
    (whole_raw U (g ≫ c) _ (parameter_comm (g ≫ c) C₀ hC₀))
    (whole_raw U (g ≫ c) _ (parameter_comm (g ≫ c) C hC))
    (whole_raw U c _ (parameter_comm c D₀ hD₀))
    (whole_raw U c _ (parameter_comm c D hD))
    (sourceMap g m) (sourceMap g n) a
    (decorated_reindex (g ≫ c) C j) (decorated_reindex c D j) (sourceMap_time g j).symm
    hDm (decorated_source c D hD g) (native_source (n := m) c g) (native_source (n := n) c g)
  unfold sourceComparison
  exact H

end

end DaggerModels.PartII.JTGraphInterpolatedSourceTime
