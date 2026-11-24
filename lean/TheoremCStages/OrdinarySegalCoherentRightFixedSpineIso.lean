import OrdinarySegalCoherentRightFixedSpinePullback

/-!
# The literal fixed triangle is the binary Segal base change

The inverse comparison uses both original pullback points. It identifies
the actual first-edge projection with the pullback of the binary Segal map.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalCoherentRightFixedSpineIso

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalCoherentRightOuterHorn
open OrdinarySegalCoherentRightFixedTriangle
open OrdinarySegalCoherentRightFixedSpine
open OrdinarySegalCoherentRightFixedSpinePullback
open OrdinarySegalCoherentRightFixedHornTargetIso (coherentRowEdge)
open OrdinarySegalCoherentRightOuterHornRow (hornRowIso rowRightHorn rowRightHorn_first)
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

private theorem lastEdge_calibration (W : Space) :
    (hornRestriction W ≫ lastEdgeRestriction W) ≫
        (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom =
      (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).hom ≫
        finalEdgeFace W := by
  rw [hornRestriction, lastEdgeRestriction,
    OrdinarySegalCoherentRightFixedHornTargetIso.lastEdgeInclusion_zero]
  rw [← diagramMappingPrecomp_comp, ← discrete.map_comp]
  dsimp only [SSet.horn₂₂.ι₁₂]
  erw [SSet.horn.ι_ι]
  exact OrdinarySegalWalkingEvaluation.simplexMappingIso_natural W
    (SimplexCategory.δ (0 : Fin 3))

private theorem middleEdge_calibration (W : Space) :
    hornRestriction W ≫ (hornRowIso W).hom ≫
        pullback.fst (targetFace W) (targetFace W) =
      (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).hom ≫
        middleEdgeFace W := by
  have h := congrArg
    (fun k ↦ (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).hom ≫ k)
    (rowRightHorn_first W)
  simpa only [rowRightHorn, Category.assoc, Iso.hom_inv_id_assoc] using h

private theorem middle_source_face (W : Space) :
    middleEdgeFace W ≫ sourceFace W =
      firstEdgeFace W ≫ sourceFace W := by
  exact SimplicialObject.δ_comp_δ_self W (i := (1 : Fin 2))

private abbrev top (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    spinePullback W H x ⟶ row W 2 :=
  pullback.fst (OrdinarySegalBinaryComparison.binaryComparison W) (spineBase W H x)

private abbrev bottom (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    spinePullback W H x ⟶ mappingFiber W x (sourceVertex W H) :=
  spineProjection W H x

private theorem top_final (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    top W H x ≫ finalEdgeFace W =
      bottom W H x ≫ pullback.snd
        (endpointArrow W) (endpointPoint W x (sourceVertex W H)) ≫
          coherentRowEdge W H := by
  have h := congrArg
    (fun k ↦ k ≫ pullback.fst (sourceFace W) (targetFace W))
    (pullback.condition
      (f := OrdinarySegalBinaryComparison.binaryComparison W)
      (g := spineBase W H x))
  have hbf := OrdinarySegalBinaryComparison.binaryComparison_fst W
  change OrdinarySegalBinaryComparison.binaryComparison W ≫
    pullback.fst (sourceFace W) (targetFace W) = finalEdgeFace W at hbf
  simpa only [top, bottom, Category.assoc, hbf,
    spineBase_lastEdge] using h

private theorem top_first (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    top W H x ≫ firstEdgeFace W =
      bottom W H x ≫ pullback.fst
        (endpointArrow W) (endpointPoint W x (sourceVertex W H)) := by
  have h := congrArg
    (fun k ↦ k ≫ pullback.snd (sourceFace W) (targetFace W))
    (pullback.condition
      (f := OrdinarySegalBinaryComparison.binaryComparison W)
      (g := spineBase W H x))
  have hbs := OrdinarySegalBinaryComparison.binaryComparison_snd W
  change OrdinarySegalBinaryComparison.binaryComparison W ≫
    pullback.snd (sourceFace W) (targetFace W) = firstEdgeFace W at hbs
  simpa only [top, bottom, Category.assoc, hbs,
    spineBase_firstEdge] using h

private theorem bottom_source (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    bottom W H x ≫ pullback.fst
        (endpointArrow W) (endpointPoint W x (sourceVertex W H)) ≫
          sourceFace W =
      bottom W H x ≫ pullback.snd
        (endpointArrow W) (endpointPoint W x (sourceVertex W H)) ≫
          SSet.yonedaEquiv.symm x := by
  have h := congrArg (fun k ↦ bottom W H x ≫ k ≫ prod.fst)
    (pullback.condition (f := endpointArrow W)
      (g := endpointPoint W x (sourceVertex W H)))
  simpa only [Category.assoc, endpointArrow_fst, endpointPoint_fst] using h

/-- Reconstruct the literal fixed horn from a binary-Segal triangle and
the original ordered first-edge fiber point. -/
private def fromSpineHorn (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    spinePullback W H x ⟶
      pullback (hornRestriction W ≫ lastEdgeRestriction W) (coherentEdge W H) :=
  pullback.lift
    (top W H x ≫ (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).inv)
    (bottom W H x ≫ pullback.snd
      (endpointArrow W) (endpointPoint W x (sourceVertex W H))) (by
        apply (cancel_mono
          (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom).mp
        calc
          (top W H x ≫
              (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).inv) ≫
              (hornRestriction W ≫ lastEdgeRestriction W) ≫
                (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom =
              top W H x ≫ finalEdgeFace W := by
            calc
              _ = top W H x ≫
                  (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).inv ≫
                    ((OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).hom ≫
                      finalEdgeFace W) := by
                simpa only [Category.assoc] using congrArg
                  (fun k ↦ top W H x ≫
                    (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).inv ≫ k)
                  (lastEdge_calibration W)
              _ = top W H x ≫ finalEdgeFace W := by
                simp only [Iso.inv_hom_id_assoc]
          _ = bottom W H x ≫ pullback.snd
              (endpointArrow W) (endpointPoint W x (sourceVertex W H)) ≫
                coherentRowEdge W H := top_final W H x
          _ = (bottom W H x ≫ pullback.snd
                (endpointArrow W) (endpointPoint W x (sourceVertex W H))) ≫
                  coherentEdge W H ≫
                    (OrdinarySegalWalkingEvaluation.simplexMappingIso W 1).hom := rfl)

private theorem fromSpineHorn_triangle (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    fromSpineHorn W H x ≫ pullback.fst
        (hornRestriction W ≫ lastEdgeRestriction W) (coherentEdge W H) ≫
          (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).hom =
      top W H x := by
  rw [fromSpineHorn, pullback.lift_fst_assoc]
  simp

private theorem fromSpineHorn_point (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    fromSpineHorn W H x ≫ pullback.snd
      (hornRestriction W ≫ lastEdgeRestriction W) (coherentEdge W H) =
        bottom W H x ≫ pullback.snd
          (endpointArrow W) (endpointPoint W x (sourceVertex W H)) := by
  simp only [fromSpineHorn, pullback.lift_snd]

private theorem restriction_composite (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    fixedRestriction W H ≫ hornComposite W H =
      pullback.fst (hornRestriction W ≫ lastEdgeRestriction W) (coherentEdge W H) ≫
        (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).hom ≫
          middleEdgeFace W := by
  have h := DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver_fst
    (hornRestriction W ≫ lastEdgeRestriction W) (lastEdgeRestriction W)
    (hornRestriction W) rfl (coherentEdge W H)
  change fixedRestriction W H ≫
      pullback.fst (lastEdgeRestriction W) (coherentEdge W H) =
    pullback.fst (hornRestriction W ≫ lastEdgeRestriction W) (coherentEdge W H) ≫
      hornRestriction W at h
  change fixedRestriction W H ≫
      pullback.fst (lastEdgeRestriction W) (coherentEdge W H) ≫
        (hornRowIso W).hom ≫ pullback.fst (targetFace W) (targetFace W) =
    pullback.fst (hornRestriction W ≫ lastEdgeRestriction W) (coherentEdge W H) ≫
      (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).hom ≫
        middleEdgeFace W
  calc
    _ = pullback.fst (hornRestriction W ≫ lastEdgeRestriction W)
          (coherentEdge W H) ≫ hornRestriction W ≫
            (hornRowIso W).hom ≫ pullback.fst (targetFace W) (targetFace W) := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ k ≫ (hornRowIso W).hom ≫
          pullback.fst (targetFace W) (targetFace W)) h
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ pullback.fst (hornRestriction W ≫ lastEdgeRestriction W)
          (coherentEdge W H) ≫ k) (middleEdge_calibration W)

private theorem fromSpineHorn_source (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    fromSpineHorn W H x ≫ fixedRestriction W H ≫ fixedHornSource W H =
      (bottom W H x ≫ pullback.snd
        (endpointArrow W) (endpointPoint W x (sourceVertex W H))) ≫
          SSet.yonedaEquiv.symm x := by
  have hmiddle : fromSpineHorn W H x ≫ fixedRestriction W H ≫
      hornComposite W H = top W H x ≫ middleEdgeFace W := by
    calc
      _ = fromSpineHorn W H x ≫
          pullback.fst (hornRestriction W ≫ lastEdgeRestriction W)
            (coherentEdge W H) ≫
            (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).hom ≫
              middleEdgeFace W := by
        simpa only [Category.assoc] using congrArg
          (fun k ↦ fromSpineHorn W H x ≫ k) (restriction_composite W H)
      _ = top W H x ≫ middleEdgeFace W := by
        simpa only [Category.assoc] using congrArg
          (fun k ↦ k ≫ middleEdgeFace W) (fromSpineHorn_triangle W H x)
  calc
    _ = top W H x ≫ middleEdgeFace W ≫ sourceFace W := by
      simpa only [fixedHornSource, Category.assoc] using congrArg
        (fun k ↦ k ≫ sourceFace W) hmiddle
    _ = top W H x ≫ firstEdgeFace W ≫ sourceFace W := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ top W H x ≫ k) (middle_source_face W)
    _ = bottom W H x ≫ pullback.fst
        (endpointArrow W) (endpointPoint W x (sourceVertex W H)) ≫
          sourceFace W := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ k ≫ sourceFace W) (top_first W H x)
    _ = _ := bottom_source W H x

/-- Reconstruct the same literal fixed triangle from the Segal pullback. -/
def spineToFixed (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    spinePullback W H x ⟶ fixedTriangle W H x :=
  pullback.lift (fromSpineHorn W H x)
    (bottom W H x ≫ pullback.snd
      (endpointArrow W) (endpointPoint W x (sourceVertex W H)))
    (fromSpineHorn_source W H x)

theorem spineToFixed_triangle (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    spineToFixed W H x ≫ fullTriangle W H x = top W H x := by
  rw [spineToFixed, fullTriangle, pullback.lift_fst_assoc]
  exact fromSpineHorn_triangle W H x

theorem spineToFixed_point (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    spineToFixed W H x ≫ trianglePoint W H x =
      bottom W H x ≫ pullback.snd
        (endpointArrow W) (endpointPoint W x (sourceVertex W H)) := by
  simp only [spineToFixed, trianglePoint, pullback.lift_snd]

theorem spineToFixed_firstEdge (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    spineToFixed W H x ≫ firstEdgeFiber W H x = bottom W H x := by
  apply pullback.hom_ext
  · rw [Category.assoc, firstEdgeFiber_edge, ← Category.assoc,
      spineToFixed_triangle]
    exact top_first W H x
  · rw [Category.assoc, firstEdgeFiber_point, spineToFixed_point]

theorem fixedToSpinePullback_rightInverse (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    spineToFixed W H x ≫ fixedToSpinePullback W H x = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, fixedToSpinePullback_triangle, spineToFixed_triangle]
    exact (Category.id_comp _).symm
  · change (spineToFixed W H x ≫ fixedToSpinePullback W H x) ≫
        spineProjection W H x = 𝟙 _ ≫ spineProjection W H x
    calc
      _ = spineToFixed W H x ≫ firstEdgeFiber W H x := by
        rw [Category.assoc, fixedToSpinePullback_firstEdge]
      _ = spineProjection W H x := spineToFixed_firstEdge W H x
      _ = 𝟙 _ ≫ spineProjection W H x := (Category.id_comp _).symm

theorem fixedToSpinePullback_leftInverse (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    fixedToSpinePullback W H x ≫ spineToFixed W H x = 𝟙 _ := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · rw [Category.assoc (fixedToSpinePullback W H x) (spineToFixed W H x)
        (pullback.fst (fixedRestriction W H ≫ fixedHornSource W H)
          (SSet.yonedaEquiv.symm x))]
      rw [spineToFixed, pullback.lift_fst, Category.id_comp]
      rw [Category.assoc, fromSpineHorn, pullback.lift_fst]
      have h := congrArg
        (fun k ↦ k ≫ (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).inv)
        (fixedToSpinePullback_triangle W H x)
      simpa only [fullTriangle, top, Category.assoc, Iso.hom_inv_id,
        Category.comp_id] using h
    · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The literal fixed triangle and the binary Segal base change are the
same object, with exact full-triangle and ordered-first-edge projections. -/
def fixedSpineIso (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    fixedTriangle W H x ≅ spinePullback W H x where
  hom := fixedToSpinePullback W H x
  inv := spineToFixed W H x
  hom_inv_id := fixedToSpinePullback_leftInverse W H x
  inv_hom_id := fixedToSpinePullback_rightInverse W H x

/-- The actual fixed-triangle first-edge projection is a Kan trivial
fibration, via the checked binary Segal comparison and the explicit iso. -/
theorem firstEdgeFiber_trivialFibration (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    trivialFibrations SSet.{0} (firstEdgeFiber W H x) := by
  have h : trivialFibrations SSet.{0}
      ((fixedSpineIso W H x).hom ≫ spineProjection W H x) :=
    (trivialFibrations SSet.{0}).comp_mem _ _
      ((trivialFibrations SSet.{0}).of_isIso _)
      (spineProjection_trivialFibration W hSegal H x)
  simpa only [fixedSpineIso, fixedToSpinePullback_firstEdge] using h

#print axioms fixedSpineIso
#print axioms firstEdgeFiber_trivialFibration

end
end DaggerModels.PartII.OrdinarySegalCoherentRightFixedSpineIso
