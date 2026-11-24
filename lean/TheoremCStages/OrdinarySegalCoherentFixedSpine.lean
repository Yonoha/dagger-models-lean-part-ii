import OrdinarySegalCoherentFixedTriangleSourceCoordinates
import OrdinarySegalBinaryComparison
import OrdinarySegalOrderedMappingFibres

/-!
# Fixed coherent first edge and the actual binary spine

The first and final edges are retained as the original horizontal face maps.
Their shared vertex comes from the binary Segal pullback, and the final
vertex comes from the same literal fixed-triangle pullback.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalCoherentFixedSpine

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalCoherentLeftOuterHorn
open OrdinarySegalCoherentFixedTriangle
open OrdinarySegalCoherentFixedTriangleSource (sourceVertex compositeToOriginalFiber)
open OrdinarySegalCoherentFixedTriangleSourceCoordinates
open OrdinarySegalCoherentFixedHornSourceIso (coherentRowEdge firstEdgeInclusion_zero)
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

/-- The actual target of the prescribed coherent first edge. -/
def targetVertex (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    (row W 0).obj (op ⦋0⦌) :=
  SSet.yonedaEquiv (coherentRowEdge W H ≫ targetFace W)

/-- The unique point leg of the literal fixed-triangle pullback. -/
def trianglePoint (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    fixedTriangle W H y ⟶ (Δ[0] : SSet.{0}) :=
  pullback.snd (fixedRestriction W H ≫ fixedHornTarget W H)
    (SSet.yonedaEquiv.symm y)

/-- The horn's chosen first edge agrees with the literal first horizontal
face of a full triangle after the checked simplex-row calibration. -/
private theorem firstEdge_calibration (W : Space) :
    (hornRestriction W ≫ firstEdgeRestriction W) ≫
        (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom =
      (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).hom ≫
        firstEdgeFace W := by
  rw [hornRestriction, firstEdgeRestriction, firstEdgeInclusion_zero]
  rw [← diagramMappingPrecomp_comp, ← discrete.map_comp, SSet.horn.ι_ι]
  exact OrdinarySegalWalkingEvaluation.simplexMappingIso_natural W
    (SimplexCategory.δ (Fin.last 2))

/-- The literal first edge of every fixed triangle is the same specified
coherent edge, including its whole vertical simplicial structure. -/
theorem fullTriangle_first (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    fullTriangle W H y ≫ firstEdgeFace W =
      trianglePoint W H y ≫ coherentRowEdge W H := by
  have h := pullback.condition
    (f := hornRestriction W ≫ firstEdgeRestriction W) (g := coherentEdge W H)
  have ht := congrArg (fun k ↦
      pullback.fst (fixedRestriction W H ≫ fixedHornTarget W H)
        (SSet.yonedaEquiv.symm y) ≫ k ≫
        (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom) h
  dsimp only at ht
  have hpoint :
      pullback.fst (fixedRestriction W H ≫ fixedHornTarget W H)
        (SSet.yonedaEquiv.symm y) ≫
          pullback.snd (hornRestriction W ≫ firstEdgeRestriction W)
            (coherentEdge W H) = trianglePoint W H y :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  calc
    fullTriangle W H y ≫ firstEdgeFace W =
        pullback.fst (fixedRestriction W H ≫ fixedHornTarget W H)
          (SSet.yonedaEquiv.symm y) ≫
          pullback.fst (hornRestriction W ≫ firstEdgeRestriction W)
            (coherentEdge W H) ≫
            ((hornRestriction W ≫ firstEdgeRestriction W) ≫
              (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom) := by
      simpa only [fullTriangle, Category.assoc] using congrArg
        (fun k ↦ pullback.fst (fixedRestriction W H ≫ fixedHornTarget W H)
          (SSet.yonedaEquiv.symm y) ≫
          pullback.fst (hornRestriction W ≫ firstEdgeRestriction W)
            (coherentEdge W H) ≫ k) (firstEdge_calibration W).symm
    _ = trianglePoint W H y ≫ coherentRowEdge W H := by
      calc
        _ = (pullback.fst (fixedRestriction W H ≫ fixedHornTarget W H)
            (SSet.yonedaEquiv.symm y) ≫
            pullback.snd (hornRestriction W ≫ firstEdgeRestriction W)
              (coherentEdge W H)) ≫ coherentEdge W H ≫
              (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom := by
            simpa only [Category.assoc] using ht
        _ = _ := by rw [hpoint]; rfl

/-- The source of the final edge is the target of the coherent first edge. -/
theorem finalEdge_source (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    fullTriangle W H y ≫ finalEdgeFace W ≫ sourceFace W =
      trianglePoint W H y ≫ SSet.yonedaEquiv.symm (targetVertex W H) := by
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
    _ = fullTriangle W H y ≫ firstEdgeFace W ≫ targetFace W := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ fullTriangle W H y ≫ k) hface
    _ = trianglePoint W H y ≫ SSet.yonedaEquiv.symm (targetVertex W H) := by
      rw [← Category.assoc, fullTriangle_first]
      simp only [targetVertex, Equiv.symm_apply_apply, Category.assoc]

/-- The target of the final edge is the original specified vertex `y`. -/
theorem finalEdge_target (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    fullTriangle W H y ≫ finalEdgeFace W ≫ targetFace W =
      trianglePoint W H y ≫ SSet.yonedaEquiv.symm y := by
  have hface : finalEdgeFace W ≫ targetFace W =
      middleEdgeFace W ≫ targetFace W := by
    exact SimplicialObject.δ_comp_δ_self W (i := (0 : Fin 2))
  have h := pullback.condition
    (f := endpointArrow W)
    (g := endpointPoint W (sourceVertex W H) y)
  have ht := congrArg (fun k ↦
      compositeToOriginalFiber W H y ≫ k ≫ prod.snd) h
  have htarget : compositeToOriginalFiber W H y ≫
        pullback.fst (endpointArrow W) (endpointPoint W (sourceVertex W H) y) ≫
          targetFace W =
      compositeToOriginalFiber W H y ≫
        pullback.snd (endpointArrow W) (endpointPoint W (sourceVertex W H) y) ≫
          SSet.yonedaEquiv.symm y := by
    simpa only [Category.assoc, endpointArrow_snd, endpointPoint_snd] using ht
  calc
    fullTriangle W H y ≫ finalEdgeFace W ≫ targetFace W =
        fullTriangle W H y ≫ middleEdgeFace W ≫ targetFace W := by
      simp only [← Category.assoc, hface]
    _ = compositeToOriginalFiber W H y ≫
        pullback.fst (endpointArrow W) (endpointPoint W (sourceVertex W H) y) ≫
          targetFace W := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ k ≫ targetFace W)
        (compositeToOriginalFiber_fst W H y).symm
    _ = compositeToOriginalFiber W H y ≫
        pullback.snd (endpointArrow W) (endpointPoint W (sourceVertex W H) y) ≫
          SSet.yonedaEquiv.symm y := htarget
    _ = trianglePoint W H y ≫ SSet.yonedaEquiv.symm y := by
      simpa only [trianglePoint, Category.assoc] using congrArg
        (fun k ↦ k ≫ SSet.yonedaEquiv.symm y)
        (compositeToOriginalFiber_snd W H y)

/-- The final edge, with both ordered endpoint equations, belongs to the
literal mapping fiber from the first edge's target to `y`. -/
def finalEdgeFiber (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    fixedTriangle W H y ⟶ mappingFiber W (targetVertex W H) y :=
  pullback.lift (fullTriangle W H y ≫ finalEdgeFace W) (trianglePoint W H y) (by
    apply prod.hom_ext
    · simpa only [endpointArrow_fst, endpointPoint_fst, Category.assoc] using
        finalEdge_source W H y
    · simpa only [endpointArrow_snd, endpointPoint_snd, Category.assoc] using
        finalEdge_target W H y)

theorem finalEdgeFiber_edge (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    finalEdgeFiber W H y ≫ pullback.fst
      (endpointArrow W) (endpointPoint W (targetVertex W H) y) =
        fullTriangle W H y ≫ finalEdgeFace W := by
  simp only [finalEdgeFiber, pullback.lift_fst]

theorem finalEdgeFiber_point (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    finalEdgeFiber W H y ≫ pullback.snd
      (endpointArrow W) (endpointPoint W (targetVertex W H) y) =
        trianglePoint W H y := by
  simp only [finalEdgeFiber, pullback.lift_snd]

#print axioms fullTriangle_first
#print axioms finalEdge_source
#print axioms finalEdge_target
#print axioms finalEdgeFiber_edge
#print axioms finalEdgeFiber_point

end
end DaggerModels.PartII.OrdinarySegalCoherentFixedSpine
