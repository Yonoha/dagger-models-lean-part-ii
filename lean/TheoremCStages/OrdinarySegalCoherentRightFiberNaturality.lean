import OrdinarySegalCoherentVertexNaturality
import OrdinarySegalCoherentRightFixedTriangleNaturality
import OrdinarySegalCoherentRightFixedSpineIso
import OrdinarySegalCoherentActualEndpoints
import OrdinarySegalOrderedMappingTransportCoordinates

/-!
# The original right fixed-triangle fiber projections is natural with its actual endpoints

The transformed coherent source is transported by its proved equality with
its original row-zero image. The same full fixed triangle is retained.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySegalCoherentRightFiberNaturality

open OrdinaryCSSLocalization (Space)
open OrdinarySegalOrderedMappingFibres (endpointArrow endpointPoint)
open OrdinarySegalOrderedMappingMaps (mappingMap mappingMap_fst)
open OrdinarySegalOrderedMappingEndpointTransport (transport)
open OrdinarySegalOrderedMappingTransportCoordinates (transport_fst)
open OrdinarySegalCoherentRightFixedTriangle (fullTriangle)
open OrdinarySegalCoherentRightFixedSpine (sourceVertex firstEdgeFiber firstEdgeFiber_edge)
open OrdinarySegalCoherentRightFixedTriangleTarget
  (targetVertex compositeToOriginalFiber compositeToOriginalFiber_fst)
open OrdinarySegalCoherentFixedEdgeNaturality (postCoherent)
open OrdinarySegalCoherentRightFixedTriangleNaturality (fixedTriangleMap fullTriangle_post)

noncomputable section

private abbrev E : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌

/-- The transformed coherent source is its actual original row-zero image. -/
theorem sourceVertex_post {W V : Space} (f : W ⟶ V)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    sourceVertex V (postCoherent f H) =
      ((f.app (op ⦋0⦌)).app (op ⦋0⦌)) (sourceVertex W H) :=
  OrdinarySegalCoherentVertexNaturality.vertex_post f H 0

/-- The source is the actual original time-zero object of the same coherent map. -/
theorem sourceVertex_actual (W : Space) (H : E ⟶ W.flip.obj (op ⦋0⦌)) :
    sourceVertex W (H ≫ (diagramRestrictionSimplexIso W.flip 0).inv) =
      SSet.yonedaEquiv (JTParameterContraction.parameterVertex ⦋1⦌ 0 ≫ H) :=
  OrdinarySegalCoherentActualEndpoints.vertex_actual W H 0

/-- The commuting square keeps the literal original mapping-fiber map,
with only the explicit equality transport of the transformed coherent source. -/
theorem firstEdgeFiber_post {W V : Space} (f : W ⟶ V)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    firstEdgeFiber W H x ≫ mappingMap f x (sourceVertex W H) =
      fixedTriangleMap f H x ≫
        firstEdgeFiber V (postCoherent f H)
          (((f.app (op ⦋0⦌)).app (op ⦋0⦌)) x) ≫
            transport V rfl (sourceVertex_post f H) := by
  let HV := postCoherent f H
  let fy := ((f.app (op ⦋0⦌)).app (op ⦋0⦌)) x
  let pW := firstEdgeFiber W H x
  let pV := firstEdgeFiber V HV fy
  let t := fixedTriangleMap f H x
  let c := transport V (rfl : fy = fy) (sourceVertex_post f H)
  change pW ≫ mappingMap f x (sourceVertex W H) = t ≫ pV ≫ c
  apply pullback.hom_ext
  · have hLeft :
        (pW ≫ mappingMap f x (sourceVertex W H)) ≫
            pullback.fst (endpointArrow V)
              (endpointPoint V
                fy (((f.app (op ⦋0⦌)).app (op ⦋0⦌)) (sourceVertex W H))) =
          (fullTriangle W H x ≫ W.map (SimplexCategory.δ (Fin.last 2)).op) ≫
            f.app (op ⦋1⦌) := by
      calc
        _ = (pW ≫ pullback.fst (endpointArrow W)
              (endpointPoint W x (sourceVertex W H))) ≫ f.app (op ⦋1⦌) := by
          simpa only [Category.assoc] using congrArg (fun k ↦ pW ≫ k)
            (mappingMap_fst f x (sourceVertex W H))
        _ = _ := by rw [firstEdgeFiber_edge]
    have hRight :
        (t ≫ pV ≫ c) ≫ pullback.fst (endpointArrow V)
            (endpointPoint V
              fy (((f.app (op ⦋0⦌)).app (op ⦋0⦌)) (sourceVertex W H))) =
          (t ≫ fullTriangle V HV fy) ≫ V.map (SimplexCategory.δ (Fin.last 2)).op := by
      calc
        _ = (t ≫ pV) ≫ pullback.fst (endpointArrow V)
              (endpointPoint V fy (sourceVertex V HV)) := by
          simpa only [Category.assoc] using congrArg (fun k ↦ t ≫ pV ≫ k)
            (transport_fst V (rfl : fy = fy) (sourceVertex_post f H))
        _ = _ := by
          simpa only [Category.assoc] using congrArg (fun k ↦ t ≫ k)
            (firstEdgeFiber_edge V HV fy)
    calc
      _ = (fullTriangle W H x ≫ W.map (SimplexCategory.δ (Fin.last 2)).op) ≫
          f.app (op ⦋1⦌) := hLeft
      _ = (fullTriangle W H x ≫ f.app (op ⦋2⦌)) ≫
          V.map (SimplexCategory.δ (Fin.last 2)).op := by
        rw [Category.assoc, f.naturality (SimplexCategory.δ (Fin.last 2)).op,
          ← Category.assoc]
      _ = (t ≫ fullTriangle V HV fy) ≫ V.map (SimplexCategory.δ (Fin.last 2)).op := by
        rw [fullTriangle_post]
      _ = _ := hRight.symm
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The transformed coherent target is its actual original row-zero image. -/
theorem targetVertex_post {W V : Space} (f : W ⟶ V)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    targetVertex V (postCoherent f H) =
      ((f.app (op ⦋0⦌)).app (op ⦋0⦌)) (targetVertex W H) :=
  OrdinarySegalCoherentVertexNaturality.vertex_post f H 1

/-- The target is the actual original time-one object of the same coherent map. -/
theorem targetVertex_actual (W : Space) (H : E ⟶ W.flip.obj (op ⦋0⦌)) :
    targetVertex W (H ≫ (diagramRestrictionSimplexIso W.flip 0).inv) =
      SSet.yonedaEquiv (JTParameterContraction.parameterVertex ⦋1⦌ 1 ≫ H) :=
  OrdinarySegalCoherentActualEndpoints.vertex_actual W H 1

/-- The commuting square keeps the literal original mapping-fiber map,
with only the explicit equality transport of the transformed coherent target. -/
theorem compositeToOriginalFiber_post {W V : Space} (f : W ⟶ V)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (x : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    compositeToOriginalFiber W H x ≫ mappingMap f x (targetVertex W H) =
      fixedTriangleMap f H x ≫
        compositeToOriginalFiber V (postCoherent f H)
          (((f.app (op ⦋0⦌)).app (op ⦋0⦌)) x) ≫
            transport V rfl (targetVertex_post f H) := by
  let HV := postCoherent f H
  let fy := ((f.app (op ⦋0⦌)).app (op ⦋0⦌)) x
  let pW := compositeToOriginalFiber W H x
  let pV := compositeToOriginalFiber V HV fy
  let t := fixedTriangleMap f H x
  let c := transport V (rfl : fy = fy) (targetVertex_post f H)
  change pW ≫ mappingMap f x (targetVertex W H) = t ≫ pV ≫ c
  apply pullback.hom_ext
  · have hLeft :
        (pW ≫ mappingMap f x (targetVertex W H)) ≫
            pullback.fst (endpointArrow V)
              (endpointPoint V
                fy (((f.app (op ⦋0⦌)).app (op ⦋0⦌)) (targetVertex W H))) =
          (fullTriangle W H x ≫ W.map (SimplexCategory.δ (1 : Fin 3)).op) ≫
            f.app (op ⦋1⦌) := by
      calc
        _ = (pW ≫ pullback.fst (endpointArrow W)
              (endpointPoint W x (targetVertex W H))) ≫ f.app (op ⦋1⦌) := by
          simpa only [Category.assoc] using congrArg (fun k ↦ pW ≫ k)
            (mappingMap_fst f x (targetVertex W H))
        _ = _ := by rw [compositeToOriginalFiber_fst]
    have hRight :
        (t ≫ pV ≫ c) ≫ pullback.fst (endpointArrow V)
            (endpointPoint V
              fy (((f.app (op ⦋0⦌)).app (op ⦋0⦌)) (targetVertex W H))) =
          (t ≫ fullTriangle V HV fy) ≫ V.map (SimplexCategory.δ (1 : Fin 3)).op := by
      calc
        _ = (t ≫ pV) ≫ pullback.fst (endpointArrow V)
              (endpointPoint V fy (targetVertex V HV)) := by
          simpa only [Category.assoc] using congrArg (fun k ↦ t ≫ pV ≫ k)
            (transport_fst V (rfl : fy = fy) (targetVertex_post f H))
        _ = _ := by
          simpa only [Category.assoc] using congrArg (fun k ↦ t ≫ k)
            (compositeToOriginalFiber_fst V HV fy)
    calc
      _ = (fullTriangle W H x ≫ W.map (SimplexCategory.δ (1 : Fin 3)).op) ≫
          f.app (op ⦋1⦌) := hLeft
      _ = (fullTriangle W H x ≫ f.app (op ⦋2⦌)) ≫
          V.map (SimplexCategory.δ (1 : Fin 3)).op := by
        rw [Category.assoc, f.naturality (SimplexCategory.δ (1 : Fin 3)).op,
          ← Category.assoc]
      _ = (t ≫ fullTriangle V HV fy) ≫ V.map (SimplexCategory.δ (1 : Fin 3)).op := by
        rw [fullTriangle_post]
      _ = _ := hRight.symm
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

#print axioms sourceVertex_post
#print axioms sourceVertex_actual
#print axioms firstEdgeFiber_post
#print axioms targetVertex_post
#print axioms targetVertex_actual
#print axioms compositeToOriginalFiber_post

end
end DaggerModels.PartII.OrdinarySegalCoherentRightFiberNaturality
