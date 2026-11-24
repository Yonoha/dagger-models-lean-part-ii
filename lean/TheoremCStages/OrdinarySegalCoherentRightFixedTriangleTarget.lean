import OrdinarySegalCoherentRightFixedTriangle
import OrdinarySegalCompositionChoices

/-!
# Original ordered mapping fiber under the fixed coherent right triangle

The free `(0,2)` edge of the same fixed right horn is identified with the
target fiber supplied by `hornTargetIso`. Fixing its source gives the
unchanged ordered mapping fiber at the literal target vertex of the
coherent last edge. Both projections retain the original row-two face
and the original point of the outer pullback.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalCoherentRightFixedTriangleTarget

open OrdinaryCSSLocalization (Space)
open OrdinarySegalCoherentRightOuterHorn
  (fixedRestriction lastEdgeRestriction coherentEdge hornRestriction)
open OrdinarySegalOrderedMappingFibres (mappingFiber endpointArrow endpointPoint)
open OrdinarySegalIteratedTargetFiberIso
  (sourceOnTarget iteratedFiber mappingFiberIso)
open OrdinarySegalCoherentRightFixedHornTargetIso
  (coherentRowEdge hornTargetIso)
open OrdinarySegalCoherentRightOuterHornRow (hornRowIso)
open OrdinarySegalCoherentRightFixedTriangle

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev E : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌
private abbrev row (W : Space) (n : ℕ) := W.obj (op ⦋n⦌)
private abbrev sourceFace (W : Space) : row W 1 ⟶ row W 0 :=
  W.map (SimplexCategory.δ (1 : Fin 2)).op
private abbrev targetFace (W : Space) : row W 1 ⟶ row W 0 :=
  W.map (SimplexCategory.δ (0 : Fin 2)).op
private abbrev middleFace (W : Space) : row W 2 ⟶ row W 1 :=
  W.map (SimplexCategory.δ (1 : Fin 3)).op

/-- The original target vertex of the literal coherent last edge. -/
def targetVertex (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    (row W 0).obj (op ⦋0⦌) :=
  SSet.yonedaEquiv (coherentRowEdge W H ≫ targetFace W)

theorem targetVertex_point (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    SSet.yonedaEquiv.symm (targetVertex W H) =
      coherentRowEdge W H ≫ targetFace W := by
  simp only [targetVertex, Equiv.symm_apply_apply]

/-- The right horn-to-target-fiber isomorphism retains the original
free composite edge as its first pullback projection. -/
theorem hornTargetIso_composite (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    (hornTargetIso W H).hom ≫
      pullback.fst (targetFace W) (coherentRowEdge W H ≫ targetFace W) =
    hornComposite W H := by
  simp [hornTargetIso, hornComposite, pullback.map,
    pullbackLeftPullbackSndIso_hom_fst, Category.assoc]

theorem hornTargetIso_source (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    (hornTargetIso W H).hom ≫
      (pullback.fst (targetFace W)
        (coherentRowEdge W H ≫ targetFace W) ≫ sourceFace W) =
    fixedHornSource W H := by
  simpa only [fixedHornSource, Category.assoc] using
    congrArg (fun z ↦ z ≫ sourceFace W) (hornTargetIso_composite W H)

/-- Fixing the first vertex in the right horn preserves the same
target-fiber isomorphism, with no change to either endpoint. -/
def fixedHornSourceFiberIso (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    fixedHornSourceFiber W H x ≅
      iteratedFiber W x (targetVertex W H) := by
  let c : pullback (targetFace W)
      (coherentRowEdge W H ≫ targetFace W) ≅
      OrdinarySegalIteratedTargetFiberIso.targetFiber W (targetVertex W H) := by
    change pullback (targetFace W) (coherentRowEdge W H ≫ targetFace W) ≅
      pullback (targetFace W)
        (SSet.yonedaEquiv.symm (targetVertex W H))
    exact pullback.congrHom rfl (targetVertex_point W H).symm
  have hc : c.hom ≫
      pullback.fst (targetFace W)
        (SSet.yonedaEquiv.symm (targetVertex W H)) =
      pullback.fst (targetFace W)
        (coherentRowEdge W H ≫ targetFace W) := by
    dsimp only [c]
    simp [pullback.congrHom]
  let r := hornTargetIso W H ≪≫ c
  have hr : r.hom ≫ sourceOnTarget W (targetVertex W H) =
      fixedHornSource W H := by
    change (hornTargetIso W H).hom ≫ c.hom ≫
      pullback.fst (targetFace W)
        (SSet.yonedaEquiv.symm (targetVertex W H)) ≫ sourceFace W =
      fixedHornSource W H
    rw [← Category.assoc c.hom
      (pullback.fst (targetFace W)
        (SSet.yonedaEquiv.symm (targetVertex W H))) (sourceFace W)]
    rw [hc]
    simpa only [Category.assoc] using hornTargetIso_source W H
  let m := pullback.map
    (fixedHornSource W H) (SSet.yonedaEquiv.symm x)
    (sourceOnTarget W (targetVertex W H))
    (SSet.yonedaEquiv.symm x)
    r.hom (𝟙 _) (𝟙 _)
    (by simpa only [Category.comp_id] using hr.symm)
    (by simp)
  haveI : IsIso m := by
    dsimp only [m]
    infer_instance
  change fixedHornSourceFiber W H x ≅
    pullback (sourceOnTarget W (targetVertex W H))
      (SSet.yonedaEquiv.symm x)
  exact asIso m

/-- The free composite edge of a fixed triangle as an original ordered
map from `x` to the coherent target vertex. -/
def compositeToOriginalFiber (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    fixedTriangle W H x ⟶ mappingFiber W x (targetVertex W H) :=
  fixedTriangleProjection W H x ≫
    (fixedHornSourceFiberIso W H x).hom ≫
    (mappingFiberIso W x (targetVertex W H)).inv

/-- The free-edge projection is a Kan trivial fibration onto the
literal original ordered mapping fiber. -/
theorem compositeToOriginalFiber_trivialFibration (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    trivialFibrations SSet.{0} (compositeToOriginalFiber W H x) := by
  have h := fixedTriangleProjection_trivialFibration W hSegal H x
  haveI : Fibration (fixedTriangleProjection W H x) :=
    ((mem_trivialFibrations_iff _).mp h).1
  haveI : WeakEquivalence (fixedTriangleProjection W H x) :=
    ((mem_trivialFibrations_iff _).mp h).2
  dsimp only [compositeToOriginalFiber]
  exact (mem_trivialFibrations_iff _).mpr ⟨inferInstance, inferInstance⟩

private theorem fixedHornFiberIso_edge (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    (fixedHornSourceFiberIso W H x).hom ≫
      pullback.fst (sourceOnTarget W (targetVertex W H))
        (SSet.yonedaEquiv.symm x) ≫
      pullback.fst (targetFace W)
        (SSet.yonedaEquiv.symm (targetVertex W H)) =
    pullback.fst (fixedHornSource W H) (SSet.yonedaEquiv.symm x) ≫
      hornComposite W H := by
  simp [fixedHornSourceFiberIso, pullback.map, pullback.congrHom,
    hornTargetIso_composite, Category.assoc]

private theorem fixedHornFiberIso_snd (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    (fixedHornSourceFiberIso W H x).hom ≫
      pullback.snd (sourceOnTarget W (targetVertex W H))
        (SSet.yonedaEquiv.symm x) =
    pullback.snd (fixedHornSource W H) (SSet.yonedaEquiv.symm x) := by
  simp [fixedHornSourceFiberIso, pullback.map, pullback.congrHom]

/-- The first projection is the literal middle face `d₁` of the unchanged
full horizontal two-simplex. -/
theorem compositeToOriginalFiber_fst (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    compositeToOriginalFiber W H x ≫
      pullback.fst (endpointArrow W)
        (endpointPoint W x (targetVertex W H)) =
    fullTriangle W H x ≫ middleFace W := by
  dsimp only [compositeToOriginalFiber]
  simp only [Category.assoc]
  rw [OrdinarySegalIteratedTargetFiberIso.mappingFiberIso_inv_fst]
  rw [fixedHornFiberIso_edge]
  rw [← Category.assoc (fixedTriangleProjection W H x)
    (pullback.fst (fixedHornSource W H) (SSet.yonedaEquiv.symm x))
    (hornComposite W H)]
  rw [fixedTriangleProjection_horn]
  simp only [Category.assoc]
  rw [← Category.assoc
    (pullback.fst (fixedRestriction W H ≫ fixedHornSource W H)
      (SSet.yonedaEquiv.symm x))
    (fixedRestriction W H) (hornComposite W H)]
  have hfixed : fixedRestriction W H ≫
      pullback.fst (lastEdgeRestriction W) (coherentEdge W H) =
      pullback.fst (hornRestriction W ≫ lastEdgeRestriction W)
        (coherentEdge W H) ≫ hornRestriction W := by
    exact DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver_fst _ _ _ _ _
  dsimp only [hornComposite]
  change pullback.fst (fixedRestriction W H ≫ fixedHornSource W H)
      (SSet.yonedaEquiv.symm x) ≫ fixedRestriction W H ≫
      pullback.fst (lastEdgeRestriction W) (coherentEdge W H) ≫
      (hornRowIso W).hom ≫
      pullback.fst (targetFace W) (targetFace W) =
    fullTriangle W H x ≫ middleFace W
  have h : hornRestriction W ≫ (hornRowIso W).hom ≫
      pullback.fst (targetFace W) (targetFace W) =
      (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).hom ≫
        middleFace W := by
    have h₀ := congrArg
      (fun z ↦ (OrdinarySegalWalkingEvaluation.simplexMappingIso W 2).hom ≫ z)
      (OrdinarySegalCoherentRightOuterHornRow.rowRightHorn_first W)
    simpa only [OrdinarySegalCoherentRightOuterHornRow.rowRightHorn,
      Category.assoc, Iso.hom_inv_id_assoc] using h₀
  calc
    _ = pullback.fst (fixedRestriction W H ≫ fixedHornSource W H)
          (SSet.yonedaEquiv.symm x) ≫
        (pullback.fst (hornRestriction W ≫ lastEdgeRestriction W)
          (coherentEdge W H) ≫ hornRestriction W) ≫
        (hornRowIso W).hom ≫
        pullback.fst (targetFace W) (targetFace W) := by
          simpa only [Category.assoc] using congrArg
            (fun z ↦ pullback.fst
              (fixedRestriction W H ≫ fixedHornSource W H)
              (SSet.yonedaEquiv.symm x) ≫ z ≫
              (hornRowIso W).hom ≫
              pullback.fst (targetFace W) (targetFace W)) hfixed
    _ = fullTriangle W H x ≫ middleFace W := by
      dsimp only [fullTriangle]
      simpa only [Category.assoc] using congrArg
        (fun z ↦ pullback.fst
          (fixedRestriction W H ≫ fixedHornSource W H)
          (SSet.yonedaEquiv.symm x) ≫
          pullback.fst (hornRestriction W ≫ lastEdgeRestriction W)
            (coherentEdge W H) ≫ z) h

/-- The second projection is the same original first-point coordinate
of the fixed triangle pullback. -/
theorem compositeToOriginalFiber_snd (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (row W 0).obj (op ⦋0⦌)) :
    compositeToOriginalFiber W H x ≫
      pullback.snd (endpointArrow W)
        (endpointPoint W x (targetVertex W H)) =
    pullback.snd (fixedRestriction W H ≫ fixedHornSource W H)
      (SSet.yonedaEquiv.symm x) := by
  dsimp only [compositeToOriginalFiber]
  simp only [Category.assoc]
  rw [OrdinarySegalIteratedTargetFiberIso.mappingFiberIso_inv_snd,
    fixedHornFiberIso_snd]
  simp [fixedTriangleProjection,
    DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver]

#print axioms targetVertex_point
#print axioms hornTargetIso_composite
#print axioms hornTargetIso_source
#print axioms fixedHornSourceFiberIso
#print axioms compositeToOriginalFiber_trivialFibration
#print axioms compositeToOriginalFiber_fst
#print axioms compositeToOriginalFiber_snd

end
end DaggerModels.PartII.OrdinarySegalCoherentRightFixedTriangleTarget
