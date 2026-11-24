import DaggerModelsPartII.JTTargetCommaPullback
import DaggerModelsPartII.GrothendieckNerveReplacement
import DaggerModelsPartII.DecoratedNecklacePresentationTargetBar

/-!
# A bar criterion for the original decorated evaluator

The full pullback-fiber nerves form a simplicial replacement. The
Grothendieck comparison and the actual target-comma equivalence transport
contractibility of this bar to the input of the original nerve Theorem A.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTTargetCommaPullbackBar

open JTTargetCommaPullback (diagram equivalence)
open DecoratedCylinderNecklacePresentation (toTarget)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable (W : Source) (x y : Vertex W)
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))

/-- The full nerve bar of original necklaces over the decorated pullbacks. -/
def bar : SSet.{0} :=
  GrothendieckNerveReplacement.fiberBar
    (BoundaryNecklaceComma.fiberDiagram (diagram W x y Q))

private theorem point_iff {X Y : SSet.{0}} (f : X ⟶ Y) [WeakEquivalence f] :
    GW (pointMap X) ↔ GW (pointMap Y) := by
  have h : f ≫ pointMap Y = pointMap X := pointIsTerminal.hom_ext _ _
  rw [← weakEquivalence_iff_GW, ← weakEquivalence_iff_GW, ← h]
  exact weakEquivalence_precomp_iff f _

/-- Contractibility of each actual target comma is equivalent to the same
condition on its full pullback bar, even when individual fibers are empty. -/
theorem comma_point_iff_bar_point :
    GW (pointMap (nerve (CostructuredArrow (toTarget W x y) Q))) ↔
      GW (pointMap (bar W x y Q)) := by
  let F := BoundaryNecklaceComma.fiberDiagram (diagram W x y Q)
  let f := nerveMap (equivalence W x y Q).functor
  let g := GrothendieckNerveReplacement.toGrothendieck F
  let h := GrothendieckNerveReplacement.toFiberBar F
  haveI : WeakEquivalence f :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence _
  haveI : WeakEquivalence g := GrothendieckNerveReplacement.toGrothendieck_weak F
  haveI : WeakEquivalence h := GrothendieckNerveReplacement.toFiberBar_weak F
  exact (point_iff f).trans ((point_iff g).symm.trans (point_iff h))

/-- The actual target functor has Kan weak nerve if all the original
fixed-target pullback bars are weakly contractible. -/
theorem target_weak_of_bar_point
    (h : ∀ Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y),
      GW (pointMap (bar W x y Q))) :
    WeakEquivalence (nerveMap (toTarget W x y)) :=
  (weakEquivalence_iff_GW _).mpr <|
    DaggerNerveTheoremA.nerveMap_GW (toTarget W x y)
      (fun Q ↦ (comma_point_iff_bar_point W x y Q).mpr (h Q))

/-- The existing calibration takes this criterion to the original evaluator. -/
theorem evaluator_weak_of_bar_point
    (h : ∀ Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y),
      GW (pointMap (bar W x y Q))) :
    WeakEquivalence (DecoratedNecklaceHomBar.evaluator W x y) :=
  (DecoratedNecklacePresentationTargetBar.evaluator_weak_iff_original_target_nerve W x y).mpr
    (target_weak_of_bar_point W x y h)

end

end DaggerModels.PartII.JTTargetCommaPullbackBar
