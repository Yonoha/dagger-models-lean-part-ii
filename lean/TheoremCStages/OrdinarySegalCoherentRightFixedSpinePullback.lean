import OrdinarySegalCoherentRightFixedSpine

/-!
# Binary Segal base change for the coherent fixed last edge

The ordered first-edge fiber maps to the literal composable pair
`(coherent last edge, free first edge)`. The resulting pullback of the
existing binary Segal comparison has a Kan trivial-fibration projection.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalCoherentRightFixedSpinePullback

open OrdinaryCSSLocalization (Space)
open OrdinarySegalCoherentRightFixedSpine
open OrdinarySegalCoherentRightFixedHornTargetIso (coherentRowEdge)
open OrdinarySegalCoherentRightFixedTriangle (fixedTriangle fullTriangle)
open OrdinarySegalOrderedMappingFibres

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev E : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌
private abbrev row (W : Space) (n : ℕ) := W.obj (op ⦋n⦌)
private abbrev sourceFace (W : Space) : row W 1 ⟶ row W 0 :=
  W.map (SimplexCategory.δ (1 : Fin 2)).op
private abbrev targetFace (W : Space) : row W 1 ⟶ row W 0 :=
  W.map (SimplexCategory.δ (0 : Fin 2)).op
private abbrev firstEdgeFace (W : Space) : row W 2 ⟶ row W 1 :=
  W.map (SimplexCategory.δ (Fin.last 2)).op
private abbrev finalEdgeFace (W : Space) : row W 2 ⟶ row W 1 :=
  W.map (SimplexCategory.δ (0 : Fin 3)).op

/-- A first edge from `x` to the source of the prescribed last edge gives
the literal ordered composable pair `(last edge, first edge)`. -/
def spineBase (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    mappingFiber W x (sourceVertex W H) ⟶
      pullback (sourceFace W) (targetFace W) :=
  pullback.lift
    (pullback.snd (endpointArrow W) (endpointPoint W x (sourceVertex W H)) ≫
      coherentRowEdge W H)
    (pullback.fst (endpointArrow W) (endpointPoint W x (sourceVertex W H))) (by
      have h := congrArg (fun k ↦ k ≫ prod.snd)
        (pullback.condition (f := endpointArrow W)
          (g := endpointPoint W x (sourceVertex W H)))
      simpa only [Category.assoc, endpointArrow_snd, endpointPoint_snd,
        sourceVertex, Equiv.symm_apply_apply] using h.symm)

theorem spineBase_lastEdge (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    spineBase W H x ≫ pullback.fst (sourceFace W) (targetFace W) =
      pullback.snd (endpointArrow W) (endpointPoint W x (sourceVertex W H)) ≫
        coherentRowEdge W H := by
  simp only [spineBase, pullback.lift_fst]

theorem spineBase_firstEdge (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    spineBase W H x ≫ pullback.snd (sourceFace W) (targetFace W) =
      pullback.fst (endpointArrow W) (endpointPoint W x (sourceVertex W H)) := by
  simp only [spineBase, pullback.lift_snd]

/-- The actual binary Segal comparison pulled back to the ordered first-edge
fiber and the prescribed whole coherent last edge. -/
def spinePullback (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) : SSet.{0} :=
  pullback (OrdinarySegalBinaryComparison.binaryComparison W) (spineBase W H x)

def spineProjection (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    spinePullback W H x ⟶ mappingFiber W x (sourceVertex W H) :=
  pullback.snd (OrdinarySegalBinaryComparison.binaryComparison W) (spineBase W H x)

/-- The second projection of the genuine binary Segal base change is a
Kan trivial fibration. -/
theorem spineProjection_trivialFibration (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    trivialFibrations SSet.{0} (spineProjection W H x) := by
  have hq := OrdinarySegalBinaryComparison.binaryComparison_trivialFibration W hSegal
  have hq' : trivialFibrations SSet.{0}
      (OrdinarySegalBinaryComparison.binaryComparison W) :=
    (mem_trivialFibrations_iff _).mpr hq
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback
      (OrdinarySegalBinaryComparison.binaryComparison W) (spineBase W H x)) hq'

/-- The unchanged right fixed triangle gives a canonical point of the
binary Segal base change, with its original full two-simplex and first edge. -/
def fixedToSpinePullback (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    fixedTriangle W H x ⟶ spinePullback W H x :=
  pullback.lift (fullTriangle W H x) (firstEdgeFiber W H x) (by
    have hbf := OrdinarySegalBinaryComparison.binaryComparison_fst W
    change OrdinarySegalBinaryComparison.binaryComparison W ≫
      pullback.fst (sourceFace W) (targetFace W) = finalEdgeFace W at hbf
    have hbs := OrdinarySegalBinaryComparison.binaryComparison_snd W
    change OrdinarySegalBinaryComparison.binaryComparison W ≫
      pullback.snd (sourceFace W) (targetFace W) = firstEdgeFace W at hbs
    apply pullback.hom_ext
    · calc
        (fullTriangle W H x ≫ OrdinarySegalBinaryComparison.binaryComparison W) ≫
            pullback.fst (sourceFace W) (targetFace W) =
          fullTriangle W H x ≫ finalEdgeFace W := by rw [Category.assoc, hbf]
        _ = trianglePoint W H x ≫ coherentRowEdge W H := fullTriangle_last W H x
        _ = firstEdgeFiber W H x ≫ pullback.snd
            (endpointArrow W) (endpointPoint W x (sourceVertex W H)) ≫
              coherentRowEdge W H := by
          rw [← firstEdgeFiber_point]
          exact Category.assoc _ _ _
        _ = (firstEdgeFiber W H x ≫ spineBase W H x) ≫
            pullback.fst (sourceFace W) (targetFace W) := by
          rw [Category.assoc, spineBase_lastEdge]
    · calc
        (fullTriangle W H x ≫ OrdinarySegalBinaryComparison.binaryComparison W) ≫
            pullback.snd (sourceFace W) (targetFace W) =
          fullTriangle W H x ≫ firstEdgeFace W := by rw [Category.assoc, hbs]
        _ = firstEdgeFiber W H x ≫ pullback.fst
            (endpointArrow W) (endpointPoint W x (sourceVertex W H)) :=
          (firstEdgeFiber_edge W H x).symm
        _ = (firstEdgeFiber W H x ≫ spineBase W H x) ≫
            pullback.snd (sourceFace W) (targetFace W) := by
          rw [Category.assoc, spineBase_firstEdge])

theorem fixedToSpinePullback_triangle (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    fixedToSpinePullback W H x ≫ pullback.fst
      (OrdinarySegalBinaryComparison.binaryComparison W) (spineBase W H x) =
        fullTriangle W H x := by
  simp only [fixedToSpinePullback, pullback.lift_fst]

theorem fixedToSpinePullback_firstEdge (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    fixedToSpinePullback W H x ≫ spineProjection W H x =
      firstEdgeFiber W H x := by
  simp only [fixedToSpinePullback, spineProjection, pullback.lift_snd]

#print axioms spineBase_lastEdge
#print axioms spineBase_firstEdge
#print axioms spineProjection_trivialFibration
#print axioms fixedToSpinePullback_triangle
#print axioms fixedToSpinePullback_firstEdge

end
end DaggerModels.PartII.OrdinarySegalCoherentRightFixedSpinePullback
