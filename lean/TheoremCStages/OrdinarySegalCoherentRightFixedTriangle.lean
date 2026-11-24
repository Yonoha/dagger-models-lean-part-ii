import OrdinarySegalCoherentRightFixedHornTargetIso
import OrdinarySegalIteratedTargetFiberIso

/-!
# Triangles with a coherent last edge and a fixed first vertex

The whole triangle, its right horn, and the first vertex remain literal
pullback data. Projection to the fixed horn is a base change of the
checked coherent right outer-horn trivial fibration.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalCoherentRightFixedTriangle

open OrdinaryCSSLocalization (Space)
open OrdinarySegalCoherentRightOuterHorn
open OrdinarySegalCoherentRightOuterHornRow

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev E : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌
private abbrev row (W : Space) (n : ℕ) := W.obj (op ⦋n⦌)

private abbrev sourceFace (W : Space) : row W 1 ⟶ row W 0 :=
  W.map (SimplexCategory.δ (1 : Fin 2)).op

private abbrev targetFace (W : Space) : row W 1 ⟶ row W 0 :=
  W.map (SimplexCategory.δ (0 : Fin 2)).op

/-- The free `(0,2)` edge of the original fixed-last-edge horn. -/
def hornComposite (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    pullback (lastEdgeRestriction W) (coherentEdge W H) ⟶ row W 1 :=
  pullback.fst (lastEdgeRestriction W) (coherentEdge W H) ≫
    (hornRowIso W).hom ≫ pullback.fst (targetFace W) (targetFace W)

/-- The source vertex of that same original free edge. -/
def fixedHornSource (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    pullback (lastEdgeRestriction W) (coherentEdge W H) ⟶ row W 0 :=
  hornComposite W H ≫ sourceFace W

/-- Fixed-last-edge horns whose free edge starts at `x`. -/
def fixedHornSourceFiber (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) : SSet.{0} :=
  pullback (fixedHornSource W H) (SSet.yonedaEquiv.symm x)

/-- Whole triangles with the actual coherent last edge and first vertex. -/
def fixedTriangle (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) : SSet.{0} :=
  pullback (fixedRestriction W H ≫ fixedHornSource W H)
    (SSet.yonedaEquiv.symm x)

/-- The unchanged full horizontal two-simplex underlying a fixed triangle. -/
def fullTriangle (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    fixedTriangle W H x ⟶ row W 2 :=
  pullback.fst (fixedRestriction W H ≫ fixedHornSource W H)
      (SSet.yonedaEquiv.symm x) ≫
    pullback.fst (hornRestriction W ≫ lastEdgeRestriction W)
      (coherentEdge W H) ≫
    (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).hom

/-- Forget the whole triangle while retaining its horn and first vertex. -/
def fixedTriangleProjection (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    fixedTriangle W H x ⟶ fixedHornSourceFiber W H x :=
  DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver
    (fixedRestriction W H ≫ fixedHornSource W H)
    (fixedHornSource W H) (fixedRestriction W H) rfl
    (SSet.yonedaEquiv.symm x)

theorem fixedTriangleProjection_horn (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    fixedTriangleProjection W H x ≫
      pullback.fst (fixedHornSource W H) (SSet.yonedaEquiv.symm x) =
    pullback.fst (fixedRestriction W H ≫ fixedHornSource W H)
      (SSet.yonedaEquiv.symm x) ≫ fixedRestriction W H :=
  DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver_fst _ _ _ _ _

/-- The fixed-triangle-to-fixed-horn projection is a Kan trivial fibration. -/
theorem fixedTriangleProjection_trivialFibration (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    trivialFibrations SSet.{0} (fixedTriangleProjection W H x) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver_isPullback
      (fixedRestriction W H ≫ fixedHornSource W H)
      (fixedHornSource W H) (fixedRestriction W H) rfl
      (SSet.yonedaEquiv.symm x)).flip
    (fixedRestriction_trivialFibration W hSegal H)

#print axioms fixedTriangleProjection_horn
#print axioms fixedTriangleProjection_trivialFibration

end
end DaggerModels.PartII.OrdinarySegalCoherentRightFixedTriangle
