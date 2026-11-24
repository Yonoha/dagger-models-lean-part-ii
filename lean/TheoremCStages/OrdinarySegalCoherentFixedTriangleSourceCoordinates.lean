import OrdinarySegalCoherentFixedTriangleSource
import OrdinarySegalCompositionChoices

/-!
# Literal coordinates of the coherent fixed-triangle source projection

The composite-edge map lands in the original ordered strict fiber. These
equalities identify its two pullback coordinates with the unchanged middle
face of the full triangle and the unchanged chosen terminal point.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySegalCoherentFixedTriangleSourceCoordinates

open OrdinaryCSSLocalization (Space)
open OrdinarySegalCoherentLeftOuterHorn
open OrdinarySegalCoherentOuterHornRow
open OrdinarySegalCoherentFixedHornSourceIso
open OrdinarySegalCoherentFixedTriangle
open OrdinarySegalCoherentFixedTriangleSource
open OrdinarySegalOrderedMappingFibres
open OrdinarySegalIteratedOrderedFiberIso

noncomputable section

private abbrev E : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌
private abbrev row (W : Space) (n : ℕ) := W.obj (op ⦋n⦌)
private abbrev sourceFace (W : Space) : row W 1 ⟶ row W 0 :=
  W.map (SimplexCategory.δ (1 : Fin 2)).op
private abbrev middleFace (W : Space) : row W 2 ⟶ row W 1 :=
  W.map (SimplexCategory.δ (1 : Fin 3)).op

private theorem iteratedIso_inv_fst (W : Space)
    (x y : (row W 0).obj (op ⦋0⦌)) :
    (mappingFiberIso W x y).inv ≫
      pullback.fst (endpointArrow W) (endpointPoint W x y) =
    pullback.fst (targetOnSource W x) (SSet.yonedaEquiv.symm y) ≫
      pullback.fst (sourceFace W) (SSet.yonedaEquiv.symm x) := by
  change (pullback.lift
    (pullback.fst (targetOnSource W x) (SSet.yonedaEquiv.symm y) ≫
      pullback.fst (sourceFace W) (SSet.yonedaEquiv.symm x))
    (pullback.snd (targetOnSource W x) (SSet.yonedaEquiv.symm y)) _) ≫
      pullback.fst (endpointArrow W) (endpointPoint W x y) = _
  simp only [pullback.lift_fst]

private theorem iteratedIso_inv_snd (W : Space)
    (x y : (row W 0).obj (op ⦋0⦌)) :
    (mappingFiberIso W x y).inv ≫
      pullback.snd (endpointArrow W) (endpointPoint W x y) =
    pullback.snd (targetOnSource W x) (SSet.yonedaEquiv.symm y) := by
  change (pullback.lift
    (pullback.fst (targetOnSource W x) (SSet.yonedaEquiv.symm y) ≫
      pullback.fst (sourceFace W) (SSet.yonedaEquiv.symm x))
    (pullback.snd (targetOnSource W x) (SSet.yonedaEquiv.symm y)) _) ≫
      pullback.snd (endpointArrow W) (endpointPoint W x y) = _
  simp only [pullback.lift_snd]

private theorem fixedHornFiberIso_edge (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    (fixedHornTargetFiberIso W H y).hom ≫
      pullback.fst (targetOnSource W (sourceVertex W H))
        (SSet.yonedaEquiv.symm y) ≫
      pullback.fst (sourceFace W)
        (SSet.yonedaEquiv.symm (sourceVertex W H)) =
    pullback.fst (fixedHornTarget W H) (SSet.yonedaEquiv.symm y) ≫
      hornComposite W H := by
  simp [fixedHornTargetFiberIso, pullback.map, pullback.congrHom,
    hornSourceIso_composite, Category.assoc]

private theorem fixedHornFiberIso_snd (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    (fixedHornTargetFiberIso W H y).hom ≫
      pullback.snd (targetOnSource W (sourceVertex W H))
        (SSet.yonedaEquiv.symm y) =
    pullback.snd (fixedHornTarget W H) (SSet.yonedaEquiv.symm y) := by
  simp [fixedHornTargetFiberIso, pullback.map, pullback.congrHom]

/-- The first projection is the literal middle face `d₁` of the unchanged
full horizontal two-simplex. -/
theorem compositeToOriginalFiber_fst (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    compositeToOriginalFiber W H y ≫
      pullback.fst (endpointArrow W)
        (endpointPoint W (sourceVertex W H) y) =
    fullTriangle W H y ≫ middleFace W := by
  dsimp only [compositeToOriginalFiber]
  simp only [Category.assoc]
  rw [iteratedIso_inv_fst]
  rw [fixedHornFiberIso_edge]
  rw [← Category.assoc (fixedTriangleProjection W H y)
    (pullback.fst (fixedHornTarget W H) (SSet.yonedaEquiv.symm y))
    (hornComposite W H)]
  rw [fixedTriangleProjection_horn]
  simp only [Category.assoc]
  rw [← Category.assoc
    (pullback.fst (fixedRestriction W H ≫ fixedHornTarget W H)
      (SSet.yonedaEquiv.symm y))
    (fixedRestriction W H) (hornComposite W H)]
  have hfixed : fixedRestriction W H ≫
      pullback.fst (firstEdgeRestriction W) (coherentEdge W H) =
      pullback.fst (hornRestriction W ≫ firstEdgeRestriction W)
        (coherentEdge W H) ≫ hornRestriction W := by
    exact DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver_fst _ _ _ _ _
  dsimp only [hornComposite]
  simp only [Category.assoc]
  rw [← Category.assoc (fixedRestriction W H)
    (pullback.fst (firstEdgeRestriction W) (coherentEdge W H))
    ((hornRowIso W).hom ≫
      pullback.snd (sourceFace W) (sourceFace W))]
  rw [hfixed]
  simp only [Category.assoc]
  dsimp only [fullTriangle, hornComposite]
  have h : hornRestriction W ≫ (hornRowIso W).hom ≫
      pullback.snd (sourceFace W) (sourceFace W) =
      (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).hom ≫
        middleFace W := by
    have h₀ := congrArg
      (fun z ↦ (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).hom ≫ z)
      (rowLeftHorn_second W)
    simpa only [rowLeftHorn, Category.assoc, Iso.hom_inv_id_assoc] using h₀
  simpa only [Category.assoc] using
    congrArg
      (fun z ↦ pullback.fst
        (fixedRestriction W H ≫ fixedHornTarget W H)
        (SSet.yonedaEquiv.symm y) ≫
        pullback.fst (hornRestriction W ≫ firstEdgeRestriction W)
          (coherentEdge W H) ≫ z) h

/-- The second projection is the same original terminal-point coordinate
of the fixed triangle pullback. -/
theorem compositeToOriginalFiber_snd (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    compositeToOriginalFiber W H y ≫
      pullback.snd (endpointArrow W)
        (endpointPoint W (sourceVertex W H) y) =
    pullback.snd (fixedRestriction W H ≫ fixedHornTarget W H)
      (SSet.yonedaEquiv.symm y) := by
  dsimp only [compositeToOriginalFiber]
  simp only [Category.assoc]
  rw [iteratedIso_inv_snd, fixedHornFiberIso_snd]
  simp [fixedTriangleProjection,
    DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver]

#print axioms compositeToOriginalFiber_fst
#print axioms compositeToOriginalFiber_snd

end
end DaggerModels.PartII.OrdinarySegalCoherentFixedTriangleSourceCoordinates
