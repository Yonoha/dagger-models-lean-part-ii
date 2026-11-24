import OrdinarySegalCoherentRightFixedTriangleTarget
import OrdinarySegalBinaryComparison

/-!
# The first edge of the literal coherent right fixed triangle

The final edge remains the prescribed whole coherent edge. The first edge
is retained as the original `δ₂` face, with ordered endpoints `(x, source H)`.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalCoherentRightFixedSpine

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalCoherentRightOuterHorn
  (hornRestriction lastEdgeRestriction coherentEdge fixedRestriction)
open OrdinarySegalCoherentRightFixedHornTargetIso
  (coherentRowEdge lastEdgeInclusion_zero)
open OrdinarySegalCoherentRightFixedTriangle
  (fixedTriangle fullTriangle fixedHornSource)
open OrdinarySegalCoherentRightFixedTriangleTarget
  (compositeToOriginalFiber compositeToOriginalFiber_fst compositeToOriginalFiber_snd)
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
private abbrev middleEdgeFace (W : Space) : row W 2 ⟶ row W 1 :=
  W.map (SimplexCategory.δ (1 : Fin 3)).op

/-- The source of the original prescribed coherent last edge. -/
def sourceVertex (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    (row W 0).obj (op ⦋0⦌) :=
  SSet.yonedaEquiv (coherentRowEdge W H ≫ sourceFace W)

/-- The unique point leg of the unchanged right fixed-triangle pullback. -/
def trianglePoint (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    fixedTriangle W H x ⟶ (Δ[0] : SSet.{0}) :=
  pullback.snd (fixedRestriction W H ≫ fixedHornSource W H)
    (SSet.yonedaEquiv.symm x)

private theorem lastEdge_calibration (W : Space) :
    (hornRestriction W ≫ lastEdgeRestriction W) ≫
        (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom =
      (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).hom ≫
        finalEdgeFace W := by
  rw [hornRestriction, lastEdgeRestriction, lastEdgeInclusion_zero]
  rw [← diagramMappingPrecomp_comp, ← discrete.map_comp]
  dsimp only [SSet.horn₂₂.ι₁₂]
  erw [SSet.horn.ι_ι]
  exact OrdinarySegalWalkingEvaluation.simplexMappingIso_natural W
    (SimplexCategory.δ (0 : Fin 3))

/-- The literal final edge of every fixed triangle is the prescribed
coherent edge, including its entire vertical simplicial structure. -/
theorem fullTriangle_last (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    fullTriangle W H x ≫ finalEdgeFace W =
      trianglePoint W H x ≫ coherentRowEdge W H := by
  have h := pullback.condition
    (f := hornRestriction W ≫ lastEdgeRestriction W) (g := coherentEdge W H)
  have ht := congrArg (fun k ↦
      pullback.fst (fixedRestriction W H ≫ fixedHornSource W H)
        (SSet.yonedaEquiv.symm x) ≫ k ≫
        (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom) h
  dsimp only at ht
  have hpoint :
      pullback.fst (fixedRestriction W H ≫ fixedHornSource W H)
        (SSet.yonedaEquiv.symm x) ≫
          pullback.snd (hornRestriction W ≫ lastEdgeRestriction W)
            (coherentEdge W H) = trianglePoint W H x :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  calc
    fullTriangle W H x ≫ finalEdgeFace W =
        pullback.fst (fixedRestriction W H ≫ fixedHornSource W H)
          (SSet.yonedaEquiv.symm x) ≫
          pullback.fst (hornRestriction W ≫ lastEdgeRestriction W)
            (coherentEdge W H) ≫
            ((hornRestriction W ≫ lastEdgeRestriction W) ≫
              (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom) := by
      simpa only [fullTriangle, Category.assoc] using congrArg
        (fun k ↦ pullback.fst (fixedRestriction W H ≫ fixedHornSource W H)
          (SSet.yonedaEquiv.symm x) ≫
          pullback.fst (hornRestriction W ≫ lastEdgeRestriction W)
            (coherentEdge W H) ≫ k) (lastEdge_calibration W).symm
    _ = trianglePoint W H x ≫ coherentRowEdge W H := by
      calc
        _ = (pullback.fst (fixedRestriction W H ≫ fixedHornSource W H)
            (SSet.yonedaEquiv.symm x) ≫
            pullback.snd (hornRestriction W ≫ lastEdgeRestriction W)
              (coherentEdge W H)) ≫ coherentEdge W H ≫
              (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom := by
            simpa only [Category.assoc] using ht
        _ = _ := by rw [hpoint]; rfl

/-- The target of the first edge is the source of the coherent last edge. -/
theorem firstEdge_target (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    fullTriangle W H x ≫ firstEdgeFace W ≫ targetFace W =
      trianglePoint W H x ≫ SSet.yonedaEquiv.symm (sourceVertex W H) := by
  have h := pullback.condition (f := sourceFace W) (g := targetFace W)
  have hbf := OrdinarySegalBinaryComparison.binaryComparison_fst W
  change OrdinarySegalBinaryComparison.binaryComparison W ≫
    pullback.fst (sourceFace W) (targetFace W) = finalEdgeFace W at hbf
  have hbs := OrdinarySegalBinaryComparison.binaryComparison_snd W
  change OrdinarySegalBinaryComparison.binaryComparison W ≫
    pullback.snd (sourceFace W) (targetFace W) = firstEdgeFace W at hbs
  have hface : finalEdgeFace W ≫ sourceFace W =
      firstEdgeFace W ≫ targetFace W := by
    calc
      _ = (OrdinarySegalBinaryComparison.binaryComparison W ≫
          pullback.fst (sourceFace W) (targetFace W)) ≫ sourceFace W := by
        rw [hbf]
      _ = (OrdinarySegalBinaryComparison.binaryComparison W ≫
          pullback.snd (sourceFace W) (targetFace W)) ≫ targetFace W := by
        simpa only [Category.assoc] using congrArg
          (fun k ↦ OrdinarySegalBinaryComparison.binaryComparison W ≫ k) h
      _ = _ := by rw [hbs]
  calc
    _ = fullTriangle W H x ≫ finalEdgeFace W ≫ sourceFace W := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ fullTriangle W H x ≫ k) hface.symm
    _ = trianglePoint W H x ≫ SSet.yonedaEquiv.symm (sourceVertex W H) := by
      rw [← Category.assoc, fullTriangle_last]
      simp only [sourceVertex, Equiv.symm_apply_apply, Category.assoc]

/-- The first edge starts at the originally fixed first vertex `x`. -/
theorem firstEdge_source (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    fullTriangle W H x ≫ firstEdgeFace W ≫ sourceFace W =
      trianglePoint W H x ≫ SSet.yonedaEquiv.symm x := by
  have hface : middleEdgeFace W ≫ sourceFace W =
      firstEdgeFace W ≫ sourceFace W :=
    SimplicialObject.δ_comp_δ_self W (i := (1 : Fin 2))
  have h := pullback.condition
    (f := endpointArrow W)
    (g := endpointPoint W x
      (OrdinarySegalCoherentRightFixedTriangleTarget.targetVertex W H))
  have hs := congrArg (fun k ↦ compositeToOriginalFiber W H x ≫ k ≫ prod.fst) h
  have hsource : compositeToOriginalFiber W H x ≫
        pullback.fst (endpointArrow W)
          (endpointPoint W x
            (OrdinarySegalCoherentRightFixedTriangleTarget.targetVertex W H)) ≫
          sourceFace W =
      compositeToOriginalFiber W H x ≫
        pullback.snd (endpointArrow W)
          (endpointPoint W x
            (OrdinarySegalCoherentRightFixedTriangleTarget.targetVertex W H)) ≫
          SSet.yonedaEquiv.symm x := by
    simpa only [Category.assoc, endpointArrow_fst, endpointPoint_fst] using hs
  calc
    _ = fullTriangle W H x ≫ middleEdgeFace W ≫ sourceFace W := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ fullTriangle W H x ≫ k) hface.symm
    _ = compositeToOriginalFiber W H x ≫
        pullback.fst (endpointArrow W)
          (endpointPoint W x
            (OrdinarySegalCoherentRightFixedTriangleTarget.targetVertex W H)) ≫
          sourceFace W := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ k ≫ sourceFace W)
        (compositeToOriginalFiber_fst W H x).symm
    _ = compositeToOriginalFiber W H x ≫
        pullback.snd (endpointArrow W)
          (endpointPoint W x
            (OrdinarySegalCoherentRightFixedTriangleTarget.targetVertex W H)) ≫
          SSet.yonedaEquiv.symm x := hsource
    _ = trianglePoint W H x ≫ SSet.yonedaEquiv.symm x := by
      simpa only [trianglePoint, Category.assoc] using congrArg
        (fun k ↦ k ≫ SSet.yonedaEquiv.symm x)
        (compositeToOriginalFiber_snd W H x)

/-- The actual first horizontal edge in the ordered mapping fiber. -/
def firstEdgeFiber (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    fixedTriangle W H x ⟶ mappingFiber W x (sourceVertex W H) :=
  pullback.lift (fullTriangle W H x ≫ firstEdgeFace W) (trianglePoint W H x) (by
    apply prod.hom_ext
    · simpa only [endpointArrow_fst, endpointPoint_fst, Category.assoc] using
        firstEdge_source W H x
    · simpa only [endpointArrow_snd, endpointPoint_snd, Category.assoc] using
        firstEdge_target W H x)

theorem firstEdgeFiber_edge (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    firstEdgeFiber W H x ≫ pullback.fst
      (endpointArrow W) (endpointPoint W x (sourceVertex W H)) =
        fullTriangle W H x ≫ firstEdgeFace W := by
  simp only [firstEdgeFiber, pullback.lift_fst]

theorem firstEdgeFiber_point (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    firstEdgeFiber W H x ≫ pullback.snd
      (endpointArrow W) (endpointPoint W x (sourceVertex W H)) =
        trianglePoint W H x := by
  simp only [firstEdgeFiber, pullback.lift_snd]

#print axioms fullTriangle_last
#print axioms firstEdge_source
#print axioms firstEdge_target
#print axioms firstEdgeFiber_edge
#print axioms firstEdgeFiber_point

end
end DaggerModels.PartII.OrdinarySegalCoherentRightFixedSpine
