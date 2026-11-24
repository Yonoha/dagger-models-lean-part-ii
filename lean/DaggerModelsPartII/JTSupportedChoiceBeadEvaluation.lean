import DaggerModelsPartII.JTSupportedNormalizationJointWeak
import DaggerModelsPartII.JTCommonCoefficientBeadLift
import DaggerModelsPartII.JTBoundaryNecklacePresentationCone
import DaggerModelsPartII.JTTargetCommaExactEvaluation
import DaggerModelsPartII.JTHomotopyTargetComma

/-! The common-coefficient cylinder choices evaluate in the original fixed-bead comma. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerSSetGluing
open DaggerOriginalProductGadget (pointMap pointIsTerminal)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTRowGraphCommonCenter

open OrdinaryJTRealization JTReversalInput JTProjectiveOrderedFiberComparison
open JTMixedGraphEndpointLifts JTNecklaceEndpointCylinder
open JTGraphFactoredPresentation (TargetComma)
open BoundaryNecklaceComma (necklaceUnder)
open JTHigherMixedGraphTargetLift (toNativeTarget)

noncomputable section

private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : SegalLocalizers.ReverseDaggerSpace.{0}}
variable {d : ℕ} {q : (Δ[d] : SSet.{0}) ⟶ realization.obj (ordinaryInput.obj W)}
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (hx : SSet.yonedaEquiv (vertex ⦋d⦌ 0 ≫ q) = rawVertex W x)
variable (hy : SSet.yonedaEquiv (vertex ⦋d⦌ (Fin.last d) ≫ q) = rawVertex W y)

private abbrev Q := JTNormalizedGraphTargetArrow.target hx hy
private abbrev code := MixedGraphCylinderTraversal.code d
private abbrev D := JTTargetCommaPullback.diagram W x y (Q hx hy)

/-- The full reduced time cylinder, indexed by the original joint choices. -/
abbrev choiceCylinders := choiceTime q hx hy ⋙ under (code (d := d))

/-- All internal endpoint-preserving necklaces over every such cylinder. -/
abbrev ChoiceResolution := BoundaryNecklaceComma.Presentation (choiceCylinders hx hy)

/-- Evaluate the paired presentation via the actual natural lift of both legs. -/
abbrev choiceToPullback : ChoiceResolution hx hy ⥤ JTTargetCommaPullback.Presentation W x y
    (Q hx hy) :=
  JTBoundaryNecklacePresentationCone.mapPresentation (D hx hy) (choiceCylinders hx hy)
    (choiceLabelIndex q hx hy) (choiceBeadLiftNatural q hx hy)

/-- Evaluate every original internal necklace in the original fixed-target comma. -/
def choiceEvaluation : ChoiceResolution hx hy ⥤ TargetComma (Q hx hy) :=
  choiceToPullback hx hy ⋙ JTTargetCommaExactEvaluation.fromPresentation W x y (Q hx hy)

/-- The whole native leg is the internal traversal followed by the previously
defined exact collapse to the original single bead. -/
theorem choiceEvaluation_native (P : ChoiceResolution hx hy) :
    necklaceUnder.map (((choiceEvaluation hx hy).obj P).hom.hom) =
      P.fiber.hom ≫ toNativeTarget d ((choiceTime q hx hy).obj P.base) := by
  change necklaceUnder.map
    (((JTTargetCommaExactEvaluation.fromPresentation W x y (Q hx hy)).obj
      ((choiceToPullback hx hy).obj P)).hom.hom) = _
  rw [JTTargetCommaExactEvaluation.native_map_obj]
  change (P.fiber.hom ≫ choiceBeadLift q hx hy P.base) ≫
      JTTargetCommaPullback.snd W x y (Q hx hy) ((choiceLabelIndex q hx hy).obj P.base) = _
  rw [Category.assoc, choiceBeadLift_snd]
  rfl

/-- The Grothendieck projection forgets the internal necklaces and is Kan weak. -/
theorem choiceResolution_projection_weak :
    WeakEquivalence (nerveMap
      (Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram (choiceCylinders hx hy)))) :=
  GrothendieckContractibleFibers.projection_weak _ (fun P ↦
    JTHomotopyTargetComma.fiber_point_GW_at (code (d := d)) ((choiceTime q hx hy).obj P))

/-- For each fixed raw simplex the actual domain of the evaluation is weakly
contractible, with all original endpoint-preserving internal maps retained. -/
theorem choiceResolution_point_GW
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    GW (pointMap (nerve (ChoiceResolution hx hy))) := by
  let P := Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram (choiceCylinders hx hy))
  letI : WeakEquivalence (nerveMap P) := choiceResolution_projection_weak hx hy
  letI : WeakEquivalence (pointMap (nerve (JointChoiceIndex hx hy))) :=
    (weakEquivalence_iff_GW _).mpr (jointChoiceIndex_point_GW hx hy hW)
  have h : nerveMap P ≫ pointMap (nerve (JointChoiceIndex hx hy)) =
      pointMap (nerve (ChoiceResolution hx hy)) := pointIsTerminal.hom_ext _ _
  rw [← h]
  exact (weakEquivalence_iff_GW _).mp inferInstance

end
end DaggerModels.PartII.JTRowGraphCommonCenter
