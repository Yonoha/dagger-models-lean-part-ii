import DaggerModelsPartII.JTGraphInterpolatedSourceComparison
import DaggerModelsPartII.JTGraphInterpolatedTransport

/-!
# Restriction and transport of a time-cylinder comparison
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphInterpolatedMixedComparison

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphLiftRestriction (restrict)
open JTGraphLiftTransport
open JTGraphInterpolatedComparison (comparisonFunctor sliceObject)
open JTGraphInterpolatedSourceComparison (sourceMap sourceComparison sliceSourceArrow)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {U V : TargetComma Q} {R S : NecklaceCode} {n : SimplexCategory}
variable (c : S ⟶ U.left.fiber.left)
variable (D : Fin (n.len + 1) → GraphLift U.left S)
variable (hD : ∀ i, (D i).collapse = c)
variable (g : R ⟶ S) (a : U ⟶ V)

include hD in
private theorem restricted_collapse (i : Fin (n.len + 1)) :
    (restrict (D i) g).collapse = g ≫ c :=
  congrArg (fun d ↦ g ≫ d) (hD i)

include hD in
private theorem transported_collapse (i : Fin (n.len + 1)) :
    ((D i).transport a.left).collapse = c ≫ a.left.fiber.left :=
  congrArg (fun d ↦ d ≫ a.left.fiber.left) (hD i)

/-- The whole-cylinder comparison after both source restriction and target transport. -/
def mixedComparison :
    comparisonFunctor (g ≫ c) (fun i ↦ restrict (D i) g)
      (restricted_collapse c D hD g) ⟶
      CostructuredArrow.map (sourceMap g n) ⋙
        comparisonFunctor (c ≫ a.left.fiber.left) (fun i ↦ (D i).transport a.left)
          (transported_collapse c D hD a) :=
  sourceComparison c D hD g ≫
    Functor.whiskerLeft (CostructuredArrow.map (sourceMap g n))
      (JTGraphInterpolatedTransport.transportComparison c D hD a)

/-- A time slice of the restricted family maps to the corresponding transported slice. -/
def mixedSliceComparison (i : Fin (n.len + 1)) :
    (comparisonFunctor (g ≫ c) (fun j ↦ restrict (D j) g)
      (restricted_collapse c D hD g)).obj (sliceObject R n i) ⟶
      (comparisonFunctor (c ≫ a.left.fiber.left) (fun j ↦ (D j).transport a.left)
        (transported_collapse c D hD a)).obj (sliceObject S n i) :=
  (mixedComparison c D hD g a).app (sliceObject R n i) ≫
    (comparisonFunctor (c ≫ a.left.fiber.left) (fun j ↦ (D j).transport a.left)
      (transported_collapse c D hD a)).map (sliceSourceArrow g n i)

end

end DaggerModels.PartII.JTGraphInterpolatedMixedComparison
