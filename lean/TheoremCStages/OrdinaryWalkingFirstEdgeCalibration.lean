import OrdinaryWalkingAlternatingPushout
import RelativeLeftOuterHornGeometry
import OriginalJoinedHornPrefix

/-!
# The first edge of every alternating walking-groupoid attachment

The chosen simplex in stage `k+2` begins with the same literal edge as
the original free-groupoid unit. The final theorem keeps that edge in the
preceding stage and uses the actual outer-horn attachment pushout.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.OrdinaryWalkingFirstEdgeCalibration

open OrdinaryWalkingAlternatingFiltration
open OrdinaryWalkingAlternatingAttachment
open OrdinaryWalkingAlternatingPushout
open RelativeLeftOuterHornGeometry

noncomputable section

private abbrev Walking := GroupoidSimplex.parameter.obj ⦋1⦌
private abbrev BinaryNerve :=
  DaggerOriginalCodiscreteNerveInjective.codiscreteNerve.obj (Fin 2)

/-- The first two letters of every chosen alternating word are `0,1`. -/
private theorem binaryWord_firstEdge (k : ℕ) :
    BinaryNerve.map (firstEdgeHom k).op (binaryWord (k + 2)) = binaryWord 1 := by
  apply nerve.ext_of_isThin
  funext j
  apply Codiscrete.ext
  fin_cases j <;> rfl

/-- The same first-edge equation in the actual walking parameter. -/
theorem alternatingSimplex_firstEdge (k : ℕ) :
    Walking.map (firstEdgeHom k).op (alternatingSimplex (k + 2)) =
      alternatingSimplex 1 := by
  have h := congrFun (walkingCodiscreteIso.inv.naturality (firstEdgeHom k).op)
    (binaryWord (k + 2))
  change Walking.map (firstEdgeHom k).op (alternatingSimplex (k + 2)) =
    walkingCodiscreteIso.inv.app (op ⦋1⦌)
      (BinaryNerve.map (firstEdgeHom k).op (binaryWord (k + 2))) at h
  rw [binaryWord_firstEdge] at h
  exact h

/-- The first attachment arrow is the literal original simplex unit. -/
theorem attachmentMap_one_eq_unit :
    attachmentMap 1 = JTCylinderCEComparison.simplexUnit.app ⦋1⦌ := by
  apply SSet.yonedaEquiv.injective
  change alternatingSimplex 1 =
    SSet.yonedaEquiv (JTCylinderCEComparison.simplexUnit.app ⦋1⦌)
  have hb : walkingCodiscreteIso.hom.app (op ⦋1⦌)
      (SSet.yonedaEquiv (JTCylinderCEComparison.simplexUnit.app ⦋1⦌)) =
        binaryWord 1 := by
    apply nerve.ext_of_isThin
    funext j
    apply Codiscrete.ext
    fin_cases j <;> rfl
  have h := congrFun (NatTrans.congr_app walkingCodiscreteIso.hom_inv_id
    (op ⦋1⦌))
    (SSet.yonedaEquiv (JTCylinderCEComparison.simplexUnit.app ⦋1⦌))
  change walkingCodiscreteIso.inv.app (op ⦋1⦌)
      (walkingCodiscreteIso.hom.app (op ⦋1⦌)
        (SSet.yonedaEquiv (JTCylinderCEComparison.simplexUnit.app ⦋1⦌))) =
      SSet.yonedaEquiv (JTCylinderCEComparison.simplexUnit.app ⦋1⦌) at h
  rw [hb] at h
  exact h

/-- Every new outer-horn critical edge is exactly the original unit. -/
theorem firstEdge_attachmentMap (k : ℕ) :
    SSet.stdSimplex.map (firstEdgeHom k) ≫ attachmentMap (k + 2) =
      JTCylinderCEComparison.simplexUnit.app ⦋1⦌ := by
  apply SSet.yonedaEquiv.injective
  rw [DaggerOriginalJoinedHornPrefix.yonedaEquiv_precomp_operator]
  change Walking.map (firstEdgeHom k).op (alternatingSimplex (k + 2)) =
    SSet.yonedaEquiv (JTCylinderCEComparison.simplexUnit.app ⦋1⦌)
  rw [alternatingSimplex_firstEdge]
  exact congrArg SSet.yonedaEquiv attachmentMap_one_eq_unit

/-- The generated literal stages increase with the stage number. -/
theorem stage_monotone : Monotone stage :=
  monotone_nat_of_le_succ stage_le_succ

/-- The critical first edge already belongs to the preceding literal
stage as the original first-stage attachment. -/
theorem firstEdge_hornToPrevious (k : ℕ) :
    firstEdgeInclusion.{0} k ≫ hornToPrevious k =
      stageAttachmentLift 1 ≫
        SSet.Subcomplex.homOfLE
          (stage_monotone (show 1 ≤ k + 1 by omega)) := by
  apply (cancel_mono (stage (k + 1)).ι).mp
  have hw := (stage_attachment_horn_isPushout k).w
  have hw' :
      (firstEdgeInclusion.{0} k ≫ hornToPrevious k) ≫ (stage (k + 1)).ι =
        (firstEdgeInclusion.{0} k ≫
          (SSet.horn (k + 2) (0 : Fin (k + 3))).ι) ≫
            attachmentMap (k + 2) := by
    simpa only [Category.assoc, SSet.Subcomplex.homOfLE_ι,
      stageAttachmentLift, SSet.Subcomplex.lift_ι] using congrArg
        (fun f ↦ firstEdgeInclusion.{0} k ≫ f ≫ (stage (k + 2)).ι) hw
  calc
    (firstEdgeInclusion.{0} k ≫ hornToPrevious k) ≫ (stage (k + 1)).ι =
        (firstEdgeInclusion.{0} k ≫
          (SSet.horn (k + 2) (0 : Fin (k + 3))).ι) ≫
            attachmentMap (k + 2) := hw'
    _ = SSet.stdSimplex.map (firstEdgeHom k) ≫ attachmentMap (k + 2) := by
      rw [firstEdgeInclusion_comp]
    _ = JTCylinderCEComparison.simplexUnit.app ⦋1⦌ := firstEdge_attachmentMap k
    _ = attachmentMap 1 := attachmentMap_one_eq_unit.symm
    _ = (stageAttachmentLift 1 ≫
        SSet.Subcomplex.homOfLE
          (stage_monotone (show 1 ≤ k + 1 by omega))) ≫
          (stage (k + 1)).ι := by
      simp only [Category.assoc, SSet.Subcomplex.homOfLE_ι,
        stageAttachmentLift, SSet.Subcomplex.lift_ι]

#print axioms alternatingSimplex_firstEdge
#print axioms attachmentMap_one_eq_unit
#print axioms firstEdge_attachmentMap
#print axioms stage_monotone
#print axioms firstEdge_hornToPrevious

end

end DaggerModels.PartII.OrdinaryWalkingFirstEdgeCalibration
