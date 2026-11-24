import OrdinarySegalCoherentFixedSpine

/-!
# Binary Segal base change for a coherent fixed first edge

The ordered final-edge fiber maps to the exact pair of composable edges by
retaining the specified whole first edge. The resulting pullback of the
checked binary Segal comparison is a Kan trivial fibration. A subsequent
comparison identifies its source with the literal fixed triangle.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalCoherentFixedSpinePullback

open OrdinaryCSSLocalization (Space)
open OrdinarySegalCoherentFixedSpine
open OrdinarySegalCoherentFixedHornSourceIso (coherentRowEdge)
open OrdinarySegalCoherentFixedTriangle (fixedTriangle fullTriangle)
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

/-- A final edge from the coherent first edge's target to `y` determines
the literal ordered pair `(final edge, coherent first edge)`. -/
def spineBase (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    mappingFiber W (targetVertex W H) y ⟶
      pullback (sourceFace W) (targetFace W) :=
  pullback.lift
    (pullback.fst (endpointArrow W) (endpointPoint W (targetVertex W H) y))
    (pullback.snd (endpointArrow W) (endpointPoint W (targetVertex W H) y) ≫
      coherentRowEdge W H) (by
        have h := congrArg (fun k ↦ k ≫ prod.fst)
          (pullback.condition (f := endpointArrow W)
            (g := endpointPoint W (targetVertex W H) y))
        simpa only [Category.assoc, endpointArrow_fst, endpointPoint_fst,
          targetVertex, Equiv.symm_apply_apply] using h)

theorem spineBase_finalEdge (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    spineBase W H y ≫ pullback.fst (sourceFace W) (targetFace W) =
      pullback.fst (endpointArrow W) (endpointPoint W (targetVertex W H) y) := by
  simp only [spineBase, pullback.lift_fst]

theorem spineBase_firstEdge (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    spineBase W H y ≫ pullback.snd (sourceFace W) (targetFace W) =
      pullback.snd (endpointArrow W) (endpointPoint W (targetVertex W H) y) ≫
        coherentRowEdge W H := by
  simp only [spineBase, pullback.lift_snd]

/-- The actual binary Segal comparison pulled back to the prescribed
first edge and the ordered final-edge mapping fiber. -/
def spinePullback (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) : SSet.{0} :=
  pullback (OrdinarySegalBinaryComparison.binaryComparison W) (spineBase W H y)

def spineProjection (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    spinePullback W H y ⟶ mappingFiber W (targetVertex W H) y :=
  pullback.snd (OrdinarySegalBinaryComparison.binaryComparison W) (spineBase W H y)

/-- Its projection to the exact ordered mapping fiber is a Kan trivial
fibration by base change of the checked degree-two Segal comparison. -/
theorem spineProjection_trivialFibration (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    trivialFibrations SSet.{0} (spineProjection W H y) := by
  have hq := OrdinarySegalBinaryComparison.binaryComparison_trivialFibration W hSegal
  have hq' : trivialFibrations SSet.{0}
      (OrdinarySegalBinaryComparison.binaryComparison W) :=
    (mem_trivialFibrations_iff _).mpr hq
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback
      (OrdinarySegalBinaryComparison.binaryComparison W) (spineBase W H y)) hq'

/-- The literal fixed triangle induces the canonical point of the
pullback of the binary Segal comparison. -/
def fixedToSpinePullback (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    fixedTriangle W H y ⟶ spinePullback W H y :=
  pullback.lift (fullTriangle W H y) (finalEdgeFiber W H y) (by
    have hbf := OrdinarySegalBinaryComparison.binaryComparison_fst W
    change OrdinarySegalBinaryComparison.binaryComparison W ≫
      pullback.fst (sourceFace W) (targetFace W) = finalEdgeFace W at hbf
    have hbs := OrdinarySegalBinaryComparison.binaryComparison_snd W
    change OrdinarySegalBinaryComparison.binaryComparison W ≫
      pullback.snd (sourceFace W) (targetFace W) = firstEdgeFace W at hbs
    apply pullback.hom_ext
    · calc
        (fullTriangle W H y ≫ OrdinarySegalBinaryComparison.binaryComparison W) ≫
            pullback.fst (sourceFace W) (targetFace W) =
          fullTriangle W H y ≫ finalEdgeFace W := by rw [Category.assoc, hbf]
        _ = finalEdgeFiber W H y ≫ pullback.fst
            (endpointArrow W) (endpointPoint W (targetVertex W H) y) :=
          (finalEdgeFiber_edge W H y).symm
        _ = (finalEdgeFiber W H y ≫ spineBase W H y) ≫
            pullback.fst (sourceFace W) (targetFace W) := by
          rw [Category.assoc, spineBase_finalEdge]
    · calc
        (fullTriangle W H y ≫ OrdinarySegalBinaryComparison.binaryComparison W) ≫
            pullback.snd (sourceFace W) (targetFace W) =
          fullTriangle W H y ≫ firstEdgeFace W := by rw [Category.assoc, hbs]
        _ = trianglePoint W H y ≫ coherentRowEdge W H := fullTriangle_first W H y
        _ = finalEdgeFiber W H y ≫ pullback.snd
            (endpointArrow W) (endpointPoint W (targetVertex W H) y) ≫
              coherentRowEdge W H := by
          rw [← finalEdgeFiber_point]
          exact Category.assoc _ _ _
        _ = (finalEdgeFiber W H y ≫ spineBase W H y) ≫
            pullback.snd (sourceFace W) (targetFace W) := by
          rw [Category.assoc, spineBase_firstEdge])

theorem fixedToSpinePullback_triangle (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    fixedToSpinePullback W H y ≫ pullback.fst
      (OrdinarySegalBinaryComparison.binaryComparison W) (spineBase W H y) =
        fullTriangle W H y := by
  simp only [fixedToSpinePullback, pullback.lift_fst]

theorem fixedToSpinePullback_finalEdge (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    fixedToSpinePullback W H y ≫ spineProjection W H y =
      finalEdgeFiber W H y := by
  simp only [fixedToSpinePullback, spineProjection, pullback.lift_snd]

#print axioms spineBase_finalEdge
#print axioms spineBase_firstEdge
#print axioms spineProjection_trivialFibration
#print axioms fixedToSpinePullback_triangle
#print axioms fixedToSpinePullback_finalEdge

end
end DaggerModels.PartII.OrdinarySegalCoherentFixedSpinePullback
