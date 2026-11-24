import DaggerModelsPartII.JTGraphInterpolatedCollapseOriginal
import DaggerModelsPartII.JTBoundaryNecklacePresentationCone

/-!
# The interpolated comparison over the original comma object
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphInterpolatedOverOriginal

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphLiftTransport
open JTGraphInterpolatedComparison (Fiber comparisonFunctor)
open JTCommaGraphPredecessor (augmentationCode)
open NecklaceCylinderAugmentation (augmentation)
open JTTargetCommaPullback (diagram toPullback equivalence)
open JTGraphInterpolatedCollapseOriginal

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {U : TargetComma Q} {S : NecklaceCode} {n : SimplexCategory}
variable (c : S ⟶ U.left.fiber.left)
variable (D : Fin (n.len + 1) → GraphLift U.left S)
variable (hD : ∀ i, (D i).collapse = c)

/-- The comparison into the pullback presentation of the original object. -/
abbrev presentationCone :=
  JTBoundaryNecklacePresentationCone.cone (diagram W x y Q) (pullbackLift c D hD)
    ((toPullback W x y Q).obj U) (indexCollapse c D hD) (timeCollapse (n := n) c)
    (pullback_collapse c D hD)

/-- The complete interpolated comparison maps naturally to the original
comma object from which the graph family was obtained. -/
def comparisonToOriginal :
    comparisonFunctor c D hD ⟶ (Functor.const (Fiber S n)).obj U :=
  Functor.whiskerRight (presentationCone c D hD) (equivalence W x y Q).inverse ≫
    (Functor.constComp (Fiber S n) ((toPullback W x y Q).obj U)
      (equivalence W x y Q).inverse).hom ≫
    (Functor.const (Fiber S n)).map ((equivalence W x y Q).unitIso.app U).inv

/-- Keep the comparison in the slice over the original comma object. -/
def overOriginal : Fiber S n ⥤ Over U :=
  Over.lift (comparisonFunctor c D hD) (comparisonToOriginal c D hD)

theorem overOriginal_forget :
    overOriginal c D hD ⋙ Over.forget U = comparisonFunctor c D hD := rfl


end

end DaggerModels.PartII.JTGraphInterpolatedOverOriginal
