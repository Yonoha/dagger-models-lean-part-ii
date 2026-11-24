import DaggerModelsPartII.JTCylinderFrame
import DaggerModelsPartII.JTCEJoyalResolution
import DaggerModelsPartII.JTWeightedBoundaryLatching

/-!
# Original Joyal Reedy cofibrancy of the standard-simplex reduced cylinder

The actual under-boundary latching arrow is the reduced-cylinder image
of the standard-simplex boundary inclusion. The existing coefficient-change
arrow isomorphism and reduced-cylinder mono theorem cover all degrees.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite Simplicial

namespace DaggerModels.PartII.JTCylinderReedy

noncomputable section

private def ordinaryJoyalModel : ModelCategory SSet.{0} :=
  DaggerActualDCHRightInducedAndMainTheoremD.ordinaryJoyalModel.{0}

private local instance : ModelCategory SSet.{0} := ordinaryJoyalModel
private local instance : ModelCategory (Under JTXiEndpointCollapse.boundary) :=
  JTEndpointCobase.underModel JTXiEndpointCollapse.boundary
private local instance : ModelCategory (Under JTXiEndpointCollapse.boundary)ᵒᵖ :=
  inferInstance
private local instance : ModelCategory
    (SimplexCategoryᵒᵖ ⥤ (Under JTXiEndpointCollapse.boundary)ᵒᵖ) :=
  simplicialReedyModelCategory (Under JTXiEndpointCollapse.boundary)ᵒᵖ

/-- The original cylinder's actual boundary image is an original Joyal
cofibration under the ordered endpoints, including the empty zero boundary. -/
theorem boundary_image_cofibration (n : ℕ) :
    cofibrations (Under JTXiEndpointCollapse.boundary)
      ((ReducedCylinder.functor JTCylinderFrame.j).map (SSet.boundary.{0} n).ι) := by
  change cofibrations SSet.{0}
    (((ReducedCylinder.functor JTCylinderFrame.j).map (SSet.boundary.{0} n).ι).right)
  change
    DaggerNativeOriginalJoyalSmithModelData.modelData.model.categoryWithCofibrations.cofibrations _
  rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelCof,
    DaggerNativeFullWeakSmithGenerators.boundary_cof]
  exact ReducedCylinder.map_mono JTCylinderFrame.j (SSet.boundary.{0} n).ι

/-- The literal standard-simplex reduced-cylinder diagram is Reedy
cofibrant under its original ordered boundary in the original Joyal model. -/
theorem under_op_isFibrant : IsFibrant JTCylinderFrame.under.op := by
  change IsFibrant
    (SSet.stdSimplex.{0}.op ⋙ (ReducedCylinder.functor JTCylinderFrame.j).op)
  apply (reedyFibrant_iff_matchingComparison _).mpr
  intro n
  have hb : fibrations (Under JTXiEndpointCollapse.boundary)ᵒᵖ
      ((ReducedCylinder.functor JTCylinderFrame.j).op.map
        (SSet.boundary.{0} n).ι.op) := by
    rw [fibrations_op]
    exact boundary_image_cofibration n
  exact ((fibrations (Under JTXiEndpointCollapse.boundary)ᵒᵖ).arrow_mk_iso_iff
    (JTWeightedBoundaryLatching.coefficientBoundaryMatchingIso
      (ReducedCylinder.functor JTCylinderFrame.j) n)).mp hb

end

end DaggerModels.PartII.JTCylinderReedy
