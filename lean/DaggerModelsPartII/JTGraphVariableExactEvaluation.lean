import DaggerModelsPartII.JTTargetCommaExactEvaluation
import DaggerModelsPartII.JTGraphVariableTotalComparison

/-! Evaluate the full variable-source resolution with its prescribed exact native
and decorated legs. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphVariableExactEvaluation

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphVariableResolutionCategory
open JTGraphVariableTimeTraversal (labels targetNatural decoratedNatural)
open JTGraphVariableTimeComparison (liftNatural)
open JTTargetCommaExactEvaluation
open BoundaryNecklaceComma (necklaceUnder)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))

/-- The actual pointwise evaluation in the original fixed-target comma. -/
def evaluation : Total Q ⥤ TargetComma Q :=
  toPresentation Q ⋙ fromPresentation W x y Q

/-- The exact evaluation has the existing natural comparison to the original object. -/
def comparison : evaluation Q ⟶ Grothendieck.forget (JTGraphVariableTimeTransport.resolutionDiagram Q) :=
  (Functor.whiskerLeft (toPresentation Q) (inverseIso W x y Q).inv) ≫ totalComparison Q

/-- The native leg is exactly the internal traversal followed by the fixed-target map. -/
theorem native_leg (P : Total Q) :
    necklaceUnder.map ((evaluation Q).obj P).hom.hom =
      P.fiber.fiber.hom ≫ (targetNatural P.base).app P.fiber.base := by
  dsimp only [evaluation, CategoryTheory.Functor.comp_obj]
  rw [native_map_obj W x y Q ((toPresentation Q).obj P)]
  change (P.fiber.fiber.hom ≫ (liftNatural P.base).app P.fiber.base) ≫
    JTTargetCommaPullback.snd W x y Q ((labels P.base).obj P.fiber.base) = _
  rw [Category.assoc]
  apply congrArg (P.fiber.fiber.hom ≫ ·)
  unfold liftNatural
  apply JTPointwisePullbackLift.lift_snd

/-- The decorated leg is exactly the internal traversal followed by the chosen graph lift. -/
theorem decorated_leg (P : Total Q) :
    ((evaluation Q).obj P).left.fiber.hom =
      P.fiber.fiber.hom ≫ (decoratedNatural P.base).app P.fiber.base := by
  dsimp only [evaluation, CategoryTheory.Functor.comp_obj]
  rw [decorated_map_obj W x y Q ((toPresentation Q).obj P)]
  change (P.fiber.fiber.hom ≫ (liftNatural P.base).app P.fiber.base) ≫
    JTTargetCommaPullback.fst W x y Q ((labels P.base).obj P.fiber.base) = _
  rw [Category.assoc]
  apply congrArg (P.fiber.fiber.hom ≫ ·)
  unfold liftNatural
  apply JTPointwisePullbackLift.lift_fst

end
end DaggerModels.PartII.JTGraphVariableExactEvaluation
