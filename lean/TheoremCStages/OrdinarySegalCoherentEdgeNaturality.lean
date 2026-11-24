import OrdinarySegalRestrictionTargetNaturality
import OrdinarySegalCoherentFixedHornSourceIso

/-!
# Whole target maps preserve the exact coherent edge and its row vertex

The target action is the actual postcomposition on the original mapping
space and on the original limit restriction. The directed simplex unit,
its ordered endpoints, and the given whole `E[1]` map are unchanged.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySegalCoherentEdgeNaturality

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalCoherentLeftOuterHorn (coherentEdge)
open OrdinarySegalCoherentFixedHornSourceIso (coherentRowEdge)

noncomputable section

private abbrev E : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌

/-- The entire coherent edge transforms by the original target map. -/
theorem coherentEdge_post {W V : Space} (f : W ⟶ V)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    coherentEdge W H ≫ diagramMappingPostcomp (discrete.obj (Δ[1] : SSet.{0})) f =
      coherentEdge V (H ≫ diagramRestrictionPost (Δ[0] : SSet.{0})
        ((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type 0)).map f)) := by
  simpa only [coherentEdge, Category.assoc] using
    (OrdinarySegalRestrictionTargetNaturality.transpose_symm_post
      (Δ[0] : SSet.{0}) (Δ[1] : SSet.{0}) f
      (JTCylinderCEComparison.simplexUnit.app ⦋1⦌ ≫ H)).symm

/-- The same naturality is the actual degree-one map of the original space. -/
theorem coherentRowEdge_post {W V : Space} (f : W ⟶ V)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    coherentRowEdge W H ≫ f.app (op ⦋1⦌) =
      coherentRowEdge V (H ≫ diagramRestrictionPost (Δ[0] : SSet.{0})
        ((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type 0)).map f)) := by
  change (coherentEdge W H ≫
      (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom) ≫ f.app (op ⦋1⦌) =
    coherentEdge V _ ≫ (OrdinarySegalWalkingEvaluation.simplexMappingIso V 1).hom
  rw [Category.assoc,
    ← OrdinarySegalRestrictionTargetNaturality.simplexMappingIso_post,
    ← Category.assoc, coherentEdge_post]

#print axioms coherentEdge_post
#print axioms coherentRowEdge_post

end
end DaggerModels.PartII.OrdinarySegalCoherentEdgeNaturality
