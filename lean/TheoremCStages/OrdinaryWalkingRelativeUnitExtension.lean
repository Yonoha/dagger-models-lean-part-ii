import OrdinaryWalkingRelativeTower
import OrdinaryWalkingInitialStageCalibration

/-!
# Relative extension of the literal original directed edge to the whole walking isomorphism

The actual unit identifies its original one-simplex domain with the first
alternating stage. Transporting the checked whole-stage extension through
this exact isomorphism retains the given edge and the prescribed whole
walking diagram in the base. Invertibility is required only for that same
original source edge.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial
open DaggerOriginalInnerHornFillers DaggerOriginalOrdinaryKanCoreEdgeMembership

namespace DaggerModels.PartII.OrdinaryWalkingRelativeUnitExtension

open OrdinaryWalkingAlternatingFiltration OrdinaryWalkingAlternatingPushout
open OrdinaryWalkingInitialStageIso OrdinaryWalkingInitialStageCalibration
open OrdinaryWalkingRelativeTower

noncomputable section

/-- Extend the original invertible directed edge over the specified whole
walking diagram in the base, retaining both literal original maps. -/
theorem edge_extension_over {C D : SSet.{0}} (p : C ⟶ D)
    (hp : DaggerNativeInnerHornFactorization.innerFibrations p)
    (hC : innerHornFillers C) (hD : innerHornFillers D)
    (e : (Δ[1] : SSet.{0}) ⟶ C)
    (β : GroupoidSimplex.parameter.obj ⦋1⦌ ⟶ D)
    (w : e ≫ p = JTCylinderCEComparison.simplexUnit.app ⦋1⦌ ≫ β)
    (he : edgeIsInvertible C (SSet.yonedaEquiv e)) :
    ∃ l : GroupoidSimplex.parameter.obj ⦋1⦌ ⟶ C,
      JTCylinderCEComparison.simplexUnit.app ⦋1⦌ ≫ l = e ∧ l ≫ p = β := by
  let u : (stage 1 : SSet.{0}) ⟶ C := initialStageIso.inv ≫ e
  have hu : u ≫ p = (stage 1).ι ≫ β := by
    dsimp only [u]
    rw [Category.assoc, w, ← Category.assoc, initialStageIso_inv_unit]
  have hue : stageAttachmentLift 1 ≫ u = e := by
    dsimp only [u]
    rw [← Category.assoc, stageAttachmentLift_one_inv, Category.id_comp]
  have huInvertible : edgeIsInvertible C
      (SSet.yonedaEquiv (stageAttachmentLift 1 ≫ u)) := by
    rw [hue]
    exact he
  obtain ⟨l, hl, hlbase⟩ := extend_entire_walking p hp hC hD u β hu huInvertible
  refine ⟨l, ?_, hlbase⟩
  calc
    JTCylinderCEComparison.simplexUnit.app ⦋1⦌ ≫ l =
        (initialStageIso.hom ≫ (stage 1).ι) ≫ l := by
      exact congrArg (fun t ↦ t ≫ l) initialStageIso_hom_ι.symm
    _ = initialStageIso.hom ≫ u := by rw [Category.assoc, hl]
    _ = e := by
      dsimp only [u]
      rw [← Category.assoc, initialStageIso.hom_inv_id, Category.id_comp]

#print axioms edge_extension_over

end

end DaggerModels.PartII.OrdinaryWalkingRelativeUnitExtension
