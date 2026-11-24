import OrdinarySegalCoherentFixedHornSourceIso
import OrdinarySegalIteratedOrderedFiberIso

/-!
# Triangles with a coherent first edge and a fixed final vertex

The whole triangle, its left horn, and the final vertex are retained as
literal pullback data. The projection to the fixed horn is a base change of
the checked coherent left outer horn trivial fibration.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalCoherentFixedTriangle

open OrdinaryCSSLocalization (Space)
open OrdinarySegalCoherentLeftOuterHorn
open OrdinarySegalCoherentOuterHornRow

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev E : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌
private abbrev row (W : Space) (n : ℕ) := W.obj (op ⦋n⦌)

private abbrev sourceFace (W : Space) : row W 1 ⟶ row W 0 :=
  W.map (SimplexCategory.δ (1 : Fin 2)).op

private abbrev targetFace (W : Space) : row W 1 ⟶ row W 0 :=
  W.map (SimplexCategory.δ (0 : Fin 2)).op

/-- The composite `(0,2)` edge of the original fixed-first-edge horn. -/
def hornComposite (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    pullback (firstEdgeRestriction W) (coherentEdge W H) ⟶ row W 1 :=
  pullback.fst (firstEdgeRestriction W) (coherentEdge W H) ≫
    (hornRowIso W).hom ≫ pullback.snd (sourceFace W) (sourceFace W)

/-- The target vertex of that same original composite edge. -/
def fixedHornTarget (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    pullback (firstEdgeRestriction W) (coherentEdge W H) ⟶ row W 0 :=
  hornComposite W H ≫ targetFace W

/-- Fixed-first-edge horns whose composite edge ends at `y`. -/
def fixedHornTargetFiber (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) : SSet.{0} :=
  pullback (fixedHornTarget W H) (SSet.yonedaEquiv.symm y)

/-- Whole triangles with the actual coherent first edge and final vertex. -/
def fixedTriangle (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) : SSet.{0} :=
  pullback (fixedRestriction W H ≫ fixedHornTarget W H)
    (SSet.yonedaEquiv.symm y)

/-- The unchanged full horizontal two-simplex underlying a fixed triangle. -/
def fullTriangle (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    fixedTriangle W H y ⟶ row W 2 :=
  pullback.fst (fixedRestriction W H ≫ fixedHornTarget W H)
      (SSet.yonedaEquiv.symm y) ≫
    pullback.fst (hornRestriction W ≫ firstEdgeRestriction W)
      (coherentEdge W H) ≫
    (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).hom

/-- Forget the whole triangle while retaining its horn and final vertex. -/
def fixedTriangleProjection (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    fixedTriangle W H y ⟶ fixedHornTargetFiber W H y :=
  DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver
    (fixedRestriction W H ≫ fixedHornTarget W H)
    (fixedHornTarget W H) (fixedRestriction W H) rfl
    (SSet.yonedaEquiv.symm y)

theorem fixedTriangleProjection_horn (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    fixedTriangleProjection W H y ≫
      pullback.fst (fixedHornTarget W H) (SSet.yonedaEquiv.symm y) =
    pullback.fst (fixedRestriction W H ≫ fixedHornTarget W H)
      (SSet.yonedaEquiv.symm y) ≫ fixedRestriction W H :=
  DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver_fst _ _ _ _ _

/-- The fixed-triangle-to-fixed-horn projection is a Kan trivial fibration. -/
theorem fixedTriangleProjection_trivialFibration (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    trivialFibrations SSet.{0} (fixedTriangleProjection W H y) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver_isPullback
      (fixedRestriction W H ≫ fixedHornTarget W H)
      (fixedHornTarget W H) (fixedRestriction W H) rfl
      (SSet.yonedaEquiv.symm y)).flip
    (fixedRestriction_trivialFibration W hSegal H)

#print axioms fixedTriangleProjection_horn
#print axioms fixedTriangleProjection_trivialFibration

end
end DaggerModels.PartII.OrdinarySegalCoherentFixedTriangle
