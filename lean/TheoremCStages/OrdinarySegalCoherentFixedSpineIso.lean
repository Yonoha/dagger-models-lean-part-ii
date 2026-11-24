import OrdinarySegalCoherentFixedSpinePullback

/-!
# The literal fixed triangle is the binary Segal base change

The inverse comparison uses both original pullback points. It identifies
the actual final-edge projection with the pullback of the binary Segal map.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalCoherentFixedSpineIso

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalCoherentLeftOuterHorn
open OrdinarySegalCoherentFixedTriangle
open OrdinarySegalCoherentFixedSpine
open OrdinarySegalCoherentFixedSpinePullback
open OrdinarySegalCoherentFixedHornSourceIso (coherentRowEdge)
open OrdinarySegalCoherentOuterHornRow (hornRowIso rowLeftHorn rowLeftHorn_second)
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

private theorem firstEdge_calibration (W : Space) :
    (hornRestriction W ≫ firstEdgeRestriction W) ≫
        (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom =
      (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).hom ≫
        firstEdgeFace W := by
  rw [hornRestriction, firstEdgeRestriction,
    OrdinarySegalCoherentFixedHornSourceIso.firstEdgeInclusion_zero]
  rw [← diagramMappingPrecomp_comp, ← discrete.map_comp, SSet.horn.ι_ι]
  exact OrdinarySegalWalkingEvaluation.simplexMappingIso_natural W
    (SimplexCategory.δ (Fin.last 2))

private theorem middleEdge_calibration (W : Space) :
    hornRestriction W ≫ (hornRowIso W).hom ≫
        pullback.snd (sourceFace W) (sourceFace W) =
      (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).hom ≫
        middleEdgeFace W := by
  have h := congrArg
    (fun k ↦ (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).hom ≫ k)
    (rowLeftHorn_second W)
  simpa only [rowLeftHorn, Category.assoc, Iso.hom_inv_id_assoc] using h

private theorem final_target_face (W : Space) :
    finalEdgeFace W ≫ targetFace W =
      middleEdgeFace W ≫ targetFace W := by
  exact SimplicialObject.δ_comp_δ_self W (i := (0 : Fin 2))

private abbrev top (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    spinePullback W H y ⟶ row W 2 :=
  pullback.fst (OrdinarySegalBinaryComparison.binaryComparison W) (spineBase W H y)

private abbrev bottom (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    spinePullback W H y ⟶ mappingFiber W (targetVertex W H) y :=
  spineProjection W H y

private theorem top_final (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    top W H y ≫ finalEdgeFace W =
      bottom W H y ≫ pullback.fst
        (endpointArrow W) (endpointPoint W (targetVertex W H) y) := by
  have h := congrArg
    (fun k ↦ k ≫ pullback.fst (sourceFace W) (targetFace W))
    (pullback.condition
      (f := OrdinarySegalBinaryComparison.binaryComparison W)
      (g := spineBase W H y))
  have hbf := OrdinarySegalBinaryComparison.binaryComparison_fst W
  change OrdinarySegalBinaryComparison.binaryComparison W ≫
    pullback.fst (sourceFace W) (targetFace W) = finalEdgeFace W at hbf
  simpa only [top, bottom, Category.assoc, hbf,
    spineBase_finalEdge] using h

private theorem top_first (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    top W H y ≫ firstEdgeFace W =
      bottom W H y ≫ pullback.snd
        (endpointArrow W) (endpointPoint W (targetVertex W H) y) ≫
          coherentRowEdge W H := by
  have h := congrArg
    (fun k ↦ k ≫ pullback.snd (sourceFace W) (targetFace W))
    (pullback.condition
      (f := OrdinarySegalBinaryComparison.binaryComparison W)
      (g := spineBase W H y))
  have hbs := OrdinarySegalBinaryComparison.binaryComparison_snd W
  change OrdinarySegalBinaryComparison.binaryComparison W ≫
    pullback.snd (sourceFace W) (targetFace W) = firstEdgeFace W at hbs
  simpa only [top, bottom, Category.assoc, hbs,
    spineBase_firstEdge] using h

private theorem bottom_target (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    bottom W H y ≫ pullback.fst
        (endpointArrow W) (endpointPoint W (targetVertex W H) y) ≫
          targetFace W =
      bottom W H y ≫ pullback.snd
        (endpointArrow W) (endpointPoint W (targetVertex W H) y) ≫
          SSet.yonedaEquiv.symm y := by
  have h := congrArg (fun k ↦ bottom W H y ≫ k ≫ prod.snd)
    (pullback.condition (f := endpointArrow W)
      (g := endpointPoint W (targetVertex W H) y))
  simpa only [Category.assoc, endpointArrow_snd, endpointPoint_snd] using h

/-- Reconstruct the literal fixed horn from a binary-Segal triangle and
the original ordered final-edge fiber point. -/
private def fromSpineHorn (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    spinePullback W H y ⟶
      pullback (hornRestriction W ≫ firstEdgeRestriction W) (coherentEdge W H) :=
  pullback.lift
    (top W H y ≫ (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).inv)
    (bottom W H y ≫ pullback.snd
      (endpointArrow W) (endpointPoint W (targetVertex W H) y)) (by
        apply (cancel_mono
          (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom).mp
        calc
          (top W H y ≫
              (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).inv) ≫
              (hornRestriction W ≫ firstEdgeRestriction W) ≫
                (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom =
              top W H y ≫ firstEdgeFace W := by
            calc
              _ = top W H y ≫
                  (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).inv ≫
                    ((OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).hom ≫
                      firstEdgeFace W) := by
                simpa only [Category.assoc] using congrArg
                  (fun k ↦ top W H y ≫
                    (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).inv ≫ k)
                  (firstEdge_calibration W)
              _ = top W H y ≫ firstEdgeFace W := by
                simp only [Iso.inv_hom_id_assoc]
          _ = bottom W H y ≫ pullback.snd
              (endpointArrow W) (endpointPoint W (targetVertex W H) y) ≫
                coherentRowEdge W H := top_first W H y
          _ = (bottom W H y ≫ pullback.snd
                (endpointArrow W) (endpointPoint W (targetVertex W H) y)) ≫
                  coherentEdge W H ≫
                    (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom := rfl)

private theorem fromSpineHorn_triangle (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    fromSpineHorn W H y ≫ pullback.fst
        (hornRestriction W ≫ firstEdgeRestriction W) (coherentEdge W H) ≫
          (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).hom =
      top W H y := by
  rw [fromSpineHorn, pullback.lift_fst_assoc]
  simp

private theorem fromSpineHorn_point (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    fromSpineHorn W H y ≫ pullback.snd
      (hornRestriction W ≫ firstEdgeRestriction W) (coherentEdge W H) =
        bottom W H y ≫ pullback.snd
          (endpointArrow W) (endpointPoint W (targetVertex W H) y) := by
  simp only [fromSpineHorn, pullback.lift_snd]

private theorem restriction_composite (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    fixedRestriction W H ≫ hornComposite W H =
      pullback.fst (hornRestriction W ≫ firstEdgeRestriction W) (coherentEdge W H) ≫
        (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).hom ≫
          middleEdgeFace W := by
  have h := DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver_fst
    (hornRestriction W ≫ firstEdgeRestriction W) (firstEdgeRestriction W)
    (hornRestriction W) rfl (coherentEdge W H)
  change fixedRestriction W H ≫
      pullback.fst (firstEdgeRestriction W) (coherentEdge W H) =
    pullback.fst (hornRestriction W ≫ firstEdgeRestriction W) (coherentEdge W H) ≫
      hornRestriction W at h
  change fixedRestriction W H ≫
      pullback.fst (firstEdgeRestriction W) (coherentEdge W H) ≫
        (hornRowIso W).hom ≫ pullback.snd (sourceFace W) (sourceFace W) =
    pullback.fst (hornRestriction W ≫ firstEdgeRestriction W) (coherentEdge W H) ≫
      (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).hom ≫
        middleEdgeFace W
  calc
    _ = pullback.fst (hornRestriction W ≫ firstEdgeRestriction W)
          (coherentEdge W H) ≫ hornRestriction W ≫
            (hornRowIso W).hom ≫ pullback.snd (sourceFace W) (sourceFace W) := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ k ≫ (hornRowIso W).hom ≫
          pullback.snd (sourceFace W) (sourceFace W)) h
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ pullback.fst (hornRestriction W ≫ firstEdgeRestriction W)
          (coherentEdge W H) ≫ k) (middleEdge_calibration W)

private theorem fromSpineHorn_target (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    fromSpineHorn W H y ≫ fixedRestriction W H ≫ fixedHornTarget W H =
      (bottom W H y ≫ pullback.snd
        (endpointArrow W) (endpointPoint W (targetVertex W H) y)) ≫
          SSet.yonedaEquiv.symm y := by
  have hmiddle : fromSpineHorn W H y ≫ fixedRestriction W H ≫
      hornComposite W H = top W H y ≫ middleEdgeFace W := by
    calc
      _ = fromSpineHorn W H y ≫
          pullback.fst (hornRestriction W ≫ firstEdgeRestriction W)
            (coherentEdge W H) ≫
            (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).hom ≫
              middleEdgeFace W := by
        simpa only [Category.assoc] using congrArg
          (fun k ↦ fromSpineHorn W H y ≫ k) (restriction_composite W H)
      _ = top W H y ≫ middleEdgeFace W := by
        simpa only [Category.assoc] using congrArg
          (fun k ↦ k ≫ middleEdgeFace W) (fromSpineHorn_triangle W H y)
  calc
    _ = top W H y ≫ middleEdgeFace W ≫ targetFace W := by
      simpa only [fixedHornTarget, Category.assoc] using congrArg
        (fun k ↦ k ≫ targetFace W) hmiddle
    _ = top W H y ≫ finalEdgeFace W ≫ targetFace W := by
      rw [← Category.assoc, final_target_face, Category.assoc]
    _ = bottom W H y ≫ pullback.fst
        (endpointArrow W) (endpointPoint W (targetVertex W H) y) ≫
          targetFace W := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ k ≫ targetFace W) (top_final W H y)
    _ = _ := bottom_target W H y

/-- Reconstruct the same literal fixed triangle from the Segal pullback. -/
def spineToFixed (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    spinePullback W H y ⟶ fixedTriangle W H y :=
  pullback.lift (fromSpineHorn W H y)
    (bottom W H y ≫ pullback.snd
      (endpointArrow W) (endpointPoint W (targetVertex W H) y))
    (fromSpineHorn_target W H y)

theorem spineToFixed_triangle (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    spineToFixed W H y ≫ fullTriangle W H y = top W H y := by
  rw [spineToFixed, fullTriangle, pullback.lift_fst_assoc]
  exact fromSpineHorn_triangle W H y

theorem spineToFixed_point (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    spineToFixed W H y ≫ trianglePoint W H y =
      bottom W H y ≫ pullback.snd
        (endpointArrow W) (endpointPoint W (targetVertex W H) y) := by
  simp only [spineToFixed, trianglePoint, pullback.lift_snd]

theorem spineToFixed_finalEdge (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    spineToFixed W H y ≫ finalEdgeFiber W H y = bottom W H y := by
  apply pullback.hom_ext
  · rw [Category.assoc, finalEdgeFiber_edge, ← Category.assoc,
      spineToFixed_triangle]
    exact top_final W H y
  · rw [Category.assoc, finalEdgeFiber_point, spineToFixed_point]

theorem fixedToSpinePullback_rightInverse (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    spineToFixed W H y ≫ fixedToSpinePullback W H y = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, fixedToSpinePullback_triangle, spineToFixed_triangle]
    exact (Category.id_comp _).symm
  · change (spineToFixed W H y ≫ fixedToSpinePullback W H y) ≫
        spineProjection W H y = 𝟙 _ ≫ spineProjection W H y
    calc
      _ = spineToFixed W H y ≫ finalEdgeFiber W H y := by
        rw [Category.assoc, fixedToSpinePullback_finalEdge]
      _ = spineProjection W H y := spineToFixed_finalEdge W H y
      _ = 𝟙 _ ≫ spineProjection W H y := (Category.id_comp _).symm

theorem fixedToSpinePullback_leftInverse (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    fixedToSpinePullback W H y ≫ spineToFixed W H y = 𝟙 _ := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · rw [Category.assoc (fixedToSpinePullback W H y) (spineToFixed W H y)
        (pullback.fst (fixedRestriction W H ≫ fixedHornTarget W H)
          (SSet.yonedaEquiv.symm y))]
      rw [spineToFixed, pullback.lift_fst, Category.id_comp]
      rw [Category.assoc, fromSpineHorn, pullback.lift_fst]
      have h := congrArg
        (fun k ↦ k ≫ (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).inv)
        (fixedToSpinePullback_triangle W H y)
      simpa only [fullTriangle, top, Category.assoc, Iso.hom_inv_id,
        Category.comp_id] using h
    · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The literal fixed triangle and the binary Segal base change are the
same object, with exact full-triangle and ordered-final-edge projections. -/
def fixedSpineIso (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    fixedTriangle W H y ≅ spinePullback W H y where
  hom := fixedToSpinePullback W H y
  inv := spineToFixed W H y
  hom_inv_id := fixedToSpinePullback_leftInverse W H y
  inv_hom_id := fixedToSpinePullback_rightInverse W H y

/-- The actual fixed-triangle final-edge projection is a Kan trivial
fibration, via the checked binary Segal comparison and the explicit iso. -/
theorem finalEdgeFiber_trivialFibration (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    trivialFibrations SSet.{0} (finalEdgeFiber W H y) := by
  have h : trivialFibrations SSet.{0}
      ((fixedSpineIso W H y).hom ≫ spineProjection W H y) :=
    (trivialFibrations SSet.{0}).comp_mem _ _
      ((trivialFibrations SSet.{0}).of_isIso _)
      (spineProjection_trivialFibration W hSegal H y)
  simpa only [fixedSpineIso, fixedToSpinePullback_finalEdge] using h

#print axioms fixedSpineIso
#print axioms finalEdgeFiber_trivialFibration

end
end DaggerModels.PartII.OrdinarySegalCoherentFixedSpineIso
