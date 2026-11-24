import OrdinarySegalCoherentFixedTriangle

/-!
# Original ordered mapping fiber under the fixed coherent triangle

The composite edge of the same fixed horn is identified with the source
fiber supplied by `hornSourceIso`. Fixing its target gives the unchanged
ordered mapping fiber at the literal source vertex of the coherent edge.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalCoherentFixedTriangleSource

open OrdinaryCSSLocalization (Space)
open OrdinarySegalOrderedMappingFibres (mappingFiber)
open OrdinarySegalIteratedOrderedFiberIso (targetOnSource iteratedFiber mappingFiberIso)
open OrdinarySegalCoherentFixedHornSourceIso (coherentRowEdge hornSourceIso)
open OrdinarySegalCoherentFixedTriangle

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev E : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌
private abbrev row (W : Space) (n : ℕ) := W.obj (op ⦋n⦌)
private abbrev sourceFace (W : Space) : row W 1 ⟶ row W 0 :=
  W.map (SimplexCategory.δ (1 : Fin 2)).op
private abbrev targetFace (W : Space) : row W 1 ⟶ row W 0 :=
  W.map (SimplexCategory.δ (0 : Fin 2)).op

/-- The original source vertex of the literal coherent first edge. -/
def sourceVertex (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    (row W 0).obj (op ⦋0⦌) :=
  SSet.yonedaEquiv (coherentRowEdge W H ≫ sourceFace W)

theorem sourceVertex_point (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    SSet.yonedaEquiv.symm (sourceVertex W H) =
      coherentRowEdge W H ≫ sourceFace W := by
  simp only [sourceVertex, Equiv.symm_apply_apply]

/-- The existing horn-to-source-fiber isomorphism retains its composite
edge as the exact first pullback projection. -/
theorem hornSourceIso_composite (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    (hornSourceIso W H).hom ≫
      pullback.fst (sourceFace W) (coherentRowEdge W H ≫ sourceFace W) =
    hornComposite W H := by
  simp [hornSourceIso, hornComposite, pullback.map, Category.assoc]

theorem hornSourceIso_target (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    (hornSourceIso W H).hom ≫
      (pullback.fst (sourceFace W)
        (coherentRowEdge W H ≫ sourceFace W) ≫ targetFace W) =
    fixedHornTarget W H := by
  simpa only [fixedHornTarget, Category.assoc] using
    congrArg (fun z ↦ z ≫ targetFace W) (hornSourceIso_composite W H)

/-- Fixing the final vertex in the horn preserves the same source-fiber
isomorphism, with no change to the source or target vertex. -/
def fixedHornTargetFiberIso (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    fixedHornTargetFiber W H y ≅ iteratedFiber W (sourceVertex W H) y := by
  let c : pullback (sourceFace W)
      (coherentRowEdge W H ≫ sourceFace W) ≅
      OrdinarySegalIteratedOrderedFiberIso.sourceFiber W (sourceVertex W H) := by
    change pullback (sourceFace W) (coherentRowEdge W H ≫ sourceFace W) ≅
      pullback (sourceFace W)
        (SSet.yonedaEquiv.symm (sourceVertex W H))
    exact pullback.congrHom rfl (sourceVertex_point W H).symm
  have hc : c.hom ≫
      pullback.fst (sourceFace W)
        (SSet.yonedaEquiv.symm (sourceVertex W H)) =
      pullback.fst (sourceFace W)
        (coherentRowEdge W H ≫ sourceFace W) := by
    dsimp only [c]
    simp [pullback.congrHom]
  let r := hornSourceIso W H ≪≫ c
  have hr : r.hom ≫ targetOnSource W (sourceVertex W H) =
      fixedHornTarget W H := by
    change (hornSourceIso W H).hom ≫ c.hom ≫
      pullback.fst (sourceFace W)
        (SSet.yonedaEquiv.symm (sourceVertex W H)) ≫ targetFace W =
      fixedHornTarget W H
    rw [← Category.assoc c.hom
      (pullback.fst (sourceFace W)
        (SSet.yonedaEquiv.symm (sourceVertex W H))) (targetFace W)]
    rw [hc]
    simpa only [Category.assoc] using hornSourceIso_target W H
  let m := pullback.map
    (fixedHornTarget W H) (SSet.yonedaEquiv.symm y)
    (targetOnSource W (sourceVertex W H))
    (SSet.yonedaEquiv.symm y)
    r.hom (𝟙 _) (𝟙 _)
    (by simpa only [Category.comp_id] using hr.symm)
    (by simp)
  haveI : IsIso m := by
    dsimp only [m]
    infer_instance
  change fixedHornTargetFiber W H y ≅
    pullback (targetOnSource W (sourceVertex W H))
      (SSet.yonedaEquiv.symm y)
  exact asIso m

/-- The actual composite edge of a fixed triangle as an original ordered
map from the coherent source vertex to `y`. -/
def compositeToOriginalFiber (W : Space)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    fixedTriangle W H y ⟶ mappingFiber W (sourceVertex W H) y :=
  fixedTriangleProjection W H y ≫
    (fixedHornTargetFiberIso W H y).hom ≫
    (mappingFiberIso W (sourceVertex W H) y).inv

/-- The composite-edge projection is a Kan trivial fibration onto the
literal original ordered mapping fiber. -/
theorem compositeToOriginalFiber_trivialFibration (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (row W 0).obj (op ⦋0⦌)) :
    trivialFibrations SSet.{0} (compositeToOriginalFiber W H y) := by
  have h := fixedTriangleProjection_trivialFibration W hSegal H y
  haveI : Fibration (fixedTriangleProjection W H y) :=
    ((mem_trivialFibrations_iff _).mp h).1
  haveI : WeakEquivalence (fixedTriangleProjection W H y) :=
    ((mem_trivialFibrations_iff _).mp h).2
  dsimp only [compositeToOriginalFiber]
  exact (mem_trivialFibrations_iff _).mpr ⟨inferInstance, inferInstance⟩

#print axioms sourceVertex_point
#print axioms hornSourceIso_composite
#print axioms hornSourceIso_target
#print axioms fixedHornTargetFiberIso
#print axioms compositeToOriginalFiber_trivialFibration

end
end DaggerModels.PartII.OrdinarySegalCoherentFixedTriangleSource
