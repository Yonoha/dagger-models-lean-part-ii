import OrdinaryWalkingInitialStageIso
import OrdinaryWalkingFirstEdgeCalibration

/-!
# The initial-stage isomorphism is the literal alternating edge map

The existing image-factor isomorphism and the alternating one-simplex have
the same composite with the unchanged first-stage inclusion: the original
simplex unit. Monomorphy of that inclusion identifies the two maps exactly.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.OrdinaryWalkingInitialStageCalibration

open OrdinaryWalkingAlternatingFiltration OrdinaryWalkingAlternatingAttachment
open OrdinaryWalkingAlternatingPushout OrdinaryWalkingFirstEdgeCalibration
open OrdinaryWalkingInitialStageIso

noncomputable section

/-- The first alternating attachment is exactly the original-unit image isomorphism. -/
theorem stageAttachmentLift_one_eq_initialStageIso :
    stageAttachmentLift 1 = initialStageIso.hom := by
  apply (cancel_mono (stage 1).ι).mp
  rw [initialStageIso_hom_ι]
  change SSet.Subcomplex.lift (attachmentMap 1) _ ≫ (stage 1).ι = _
  rw [SSet.Subcomplex.lift_ι]
  exact attachmentMap_one_eq_unit

/-- The initial attachment followed by the original-unit inverse is the identity. -/
theorem stageAttachmentLift_one_inv :
    stageAttachmentLift 1 ≫ initialStageIso.inv = 𝟙 (Δ[1] : SSet.{0}) := by
  rw [stageAttachmentLift_one_eq_initialStageIso, initialStageIso.hom_inv_id]

#print axioms stageAttachmentLift_one_eq_initialStageIso
#print axioms stageAttachmentLift_one_inv

end

end DaggerModels.PartII.OrdinaryWalkingInitialStageCalibration
