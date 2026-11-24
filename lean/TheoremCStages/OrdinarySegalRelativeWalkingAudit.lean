import OrdinarySegalRelativeFoundationsAudit
import OrdinarySegalRelativeLeftOuterHorn
import OrdinaryWalkingRelativeUnitExtension
import OrdinarySegalRestrictionTranspose
import OrdinaryWalkingParameterInvertibleEdge

/-!
# Whole walking extension at the exact original reverse-dagger Segal input

The actual ordinary input of the original raw JT transpose supplies the
inner fibration and both quasicategories needed by the whole relative
walking-extension theorem. The original directed edge and prescribed base
walking map are retained. Ordinary completeness and raw ordered weakness
are not assumed. This is an import/axiom audit, not a Comparator Challenge
or a proof of the original Theorem C.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerOriginalInnerHornFillers DaggerOriginalOrdinaryKanCoreEdgeMembership

namespace DaggerModels.PartII.OrdinarySegalRelativeWalkingAudit

open OrdinaryCSSLocalization (Space)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- The exact ordinary input admits relative extensions of its original
invertible directed edge over any prescribed whole base walking diagram. -/
theorem originalInput_relative_walking_extension
    (W : SegalLocalizers.ReverseDaggerSpace.{0})
    (hW : letI : ModelCategory SegalLocalizers.ReverseDaggerSpace.{0} :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hSegal : SegalLocalizers.segalCondition W)
    {K L : SSet.{0}} (v : K ⟶ L) [Mono v]
    (e : (Δ[1] : SSet.{0}) ⟶
      diagramRestriction L (RawOrdinaryJTQuillenTranspose.input W).flip)
    (β : GroupoidSimplex.parameter.obj ⦋1⦌ ⟶
      diagramRestriction K (RawOrdinaryJTQuillenTranspose.input W).flip)
    (w : e ≫ diagramRestrictionPre v (RawOrdinaryJTQuillenTranspose.input W).flip =
      JTCylinderCEComparison.simplexUnit.app ⦋1⦌ ≫ β)
    (he : edgeIsInvertible
      (diagramRestriction L (RawOrdinaryJTQuillenTranspose.input W).flip)
      (SSet.yonedaEquiv e)) :
    ∃ l : GroupoidSimplex.parameter.obj ⦋1⦌ ⟶
        diagramRestriction L (RawOrdinaryJTQuillenTranspose.input W).flip,
      JTCylinderCEComparison.simplexUnit.app ⦋1⦌ ≫ l = e ∧
        l ≫ diagramRestrictionPre v (RawOrdinaryJTQuillenTranspose.input W).flip = β := by
  let V := RawOrdinaryJTQuillenTranspose.input W
  have : IsFibrant V := OrdinaryJTOrdinaryInputReedy.ordinaryInput_injectiveFibrant W hW
  have hV : OrdinaryCSSConditions.segalCondition V :=
    OrdinaryJTOrdinaryInputSegal.ordinaryInput_segalCondition W hSegal
  have hC : innerHornFillers (diagramRestriction L V.flip) :=
    (innerHornFillers_iff_native_quasicategory _).mpr
      (OrdinarySegalHorizontalRestrictions.restriction_quasicategory V hV L)
  have hD : innerHornFillers (diagramRestriction K V.flip) :=
    (innerHornFillers_iff_native_quasicategory _).mpr
      (OrdinarySegalHorizontalRestrictions.restriction_quasicategory V hV K)
  exact OrdinaryWalkingRelativeUnitExtension.edge_extension_over
    (diagramRestrictionPre v V.flip)
    (OrdinarySegalHorizontalRestrictions.restriction_innerFibration V hV v)
    hC hD e β w he

#print axioms originalInput_relative_walking_extension
#print axioms OrdinaryWalkingRelativeUnitExtension.edge_extension_over
#print axioms RelativeSelectedLeftOuterHornFilling.selected_left_outer_horn_filler_over
#print axioms OrdinaryWalkingAlternatingPushout.stage_attachment_horn_isPushout
#print axioms OrdinaryWalkingFirstEdgeCalibration.firstEdge_hornToPrevious
#print axioms NatSubcomplexGluing.ι_desc
#print axioms OrdinarySegalRestrictionTranspose.simplexUnit_transpose
#print axioms OrdinaryWalkingParameterInvertibleEdge.simplexUnit_image_invertible
#print axioms RawOrdinaryJTUnitCSSWeak.rawTranspose_cssWeak
#print axioms JTTheoremCFromOriginalRawOrderedUnit.statement_of_originalRawOrderedUnit

end

end DaggerModels.PartII.OrdinarySegalRelativeWalkingAudit
