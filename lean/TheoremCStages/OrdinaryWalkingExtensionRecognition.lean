import OrdinaryWalkingParameterCalibration
import OrdinaryWalkingParameterInvertibleEdge
import NativeHoIsoWalkingExtension

/-!
# Recognition of the original walking extension by native invertibility

The existing native theorem extends an invertible edge to the entire walking
isomorphism. The exact parameter isomorphism also preserves its directed edge,
so the same criterion applies to the original groupoid-completed simplex.
No homotopy category for Segal spaces is reconstructed here.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.OrdinaryWalkingExtensionRecognition

open OrdinaryWalkingParameterCalibration (parameterWalkingIso)
open DaggerOriginalOrdinaryKanCoreEdgeMembership (edgeIsInvertible)
open DaggerOriginalQuasicategoryInverseEdgeRepresentatives
  (edgeIsInvertible_iff_original_homMk_isIso)

noncomputable section

/-- The existing parameter comparison preserves the original directed edge. -/
theorem simplexUnit_parameterWalkingIso :
    JTCylinderCEComparison.simplexUnit.app ⦋1⦌ ≫ parameterWalkingIso.hom =
      DaggerNativeWalkingEdgeKanInclusion.edgeInclusion.{0} := by
  apply NatTrans.ext
  funext q s
  apply nerve.ext_of_isThin
  funext i
  rfl

/-- An edge extends through the original walking parameter exactly when its
native homotopy-category class is invertible. -/
theorem walking_extension_iff (Q : SSet.{0}) [Q.Quasicategory]
    (u : (Δ[1] : SSet.{0}) ⟶ Q) :
    (∃ H : GroupoidSimplex.parameter.obj ⦋1⦌ ⟶ Q,
      JTCylinderCEComparison.simplexUnit.app ⦋1⦌ ≫ H = u) ↔
      edgeIsInvertible Q (SSet.yonedaEquiv u) := by
  constructor
  · rintro ⟨H, rfl⟩
    exact OrdinaryWalkingParameterInvertibleEdge.simplexUnit_image_invertible Q H
  · intro hu
    let e : SSet.Edge (Q.δ 1 (SSet.yonedaEquiv u)) (Q.δ 0 (SSet.yonedaEquiv u)) :=
      SSet.Edge.mk (SSet.yonedaEquiv u) rfl rfl
    have : IsIso (SSet.Truncated.HomotopyCategory.homMk e) :=
      (edgeIsInvertible_iff_original_homMk_isIso Q e).mp hu
    obtain ⟨H, hH⟩ := DaggerNativeHoIsoWalkingExtension.invertible_edge_extension Q e
    refine ⟨parameterWalkingIso.hom ≫ H, ?_⟩
    rw [← Category.assoc, simplexUnit_parameterWalkingIso, hH]
    exact Equiv.symm_apply_apply SSet.yonedaEquiv u

#print axioms simplexUnit_parameterWalkingIso
#print axioms walking_extension_iff

end

end DaggerModels.PartII.OrdinaryWalkingExtensionRecognition
