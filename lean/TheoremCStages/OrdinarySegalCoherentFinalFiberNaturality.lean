import OrdinarySegalCoherentCompositeFiberNaturality
import OrdinarySegalCoherentFixedSpine
import OrdinarySegalCoherentActualEndpoints

/-!
# The original final-edge fiber projection is natural with its actual endpoints

The transformed coherent target is transported by its proved equality with
its original row-zero image. The same full fixed triangle is retained.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySegalCoherentFinalFiberNaturality

open OrdinaryCSSLocalization (Space)
open OrdinarySegalOrderedMappingFibres (endpointArrow endpointPoint)
open OrdinarySegalOrderedMappingMaps (mappingMap mappingMap_fst)
open OrdinarySegalOrderedMappingEndpointTransport (transport)
open OrdinarySegalOrderedMappingTransportCoordinates (transport_fst)
open OrdinarySegalCoherentFixedTriangle (fullTriangle)
open OrdinarySegalCoherentFixedSpine (targetVertex finalEdgeFiber finalEdgeFiber_edge)
open OrdinarySegalCoherentFixedEdgeNaturality (postCoherent)
open OrdinarySegalCoherentFixedTriangleNaturality (fixedTriangleMap fullTriangle_post)

noncomputable section

private abbrev E : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌

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
theorem finalEdgeFiber_post {W V : Space} (f : W ⟶ V)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    finalEdgeFiber W H y ≫ mappingMap f (targetVertex W H) y =
      fixedTriangleMap f H y ≫
        finalEdgeFiber V (postCoherent f H)
          (((f.app (op ⦋0⦌)).app (op ⦋0⦌)) y) ≫
            transport V (targetVertex_post f H) rfl := by
  let HV := postCoherent f H
  let fy := ((f.app (op ⦋0⦌)).app (op ⦋0⦌)) y
  let pW := finalEdgeFiber W H y
  let pV := finalEdgeFiber V HV fy
  let t := fixedTriangleMap f H y
  let c := transport V (targetVertex_post f H) (rfl : fy = fy)
  change pW ≫ mappingMap f (targetVertex W H) y = t ≫ pV ≫ c
  apply pullback.hom_ext
  · have hLeft :
        (pW ≫ mappingMap f (targetVertex W H) y) ≫
            pullback.fst (endpointArrow V)
              (endpointPoint V
                (((f.app (op ⦋0⦌)).app (op ⦋0⦌)) (targetVertex W H)) fy) =
          (fullTriangle W H y ≫ W.map (SimplexCategory.δ (0 : Fin 3)).op) ≫
            f.app (op ⦋1⦌) := by
      calc
        _ = (pW ≫ pullback.fst (endpointArrow W)
              (endpointPoint W (targetVertex W H) y)) ≫ f.app (op ⦋1⦌) := by
          simpa only [Category.assoc] using congrArg (fun k ↦ pW ≫ k)
            (mappingMap_fst f (targetVertex W H) y)
        _ = _ := by rw [finalEdgeFiber_edge]
    have hRight :
        (t ≫ pV ≫ c) ≫ pullback.fst (endpointArrow V)
            (endpointPoint V
              (((f.app (op ⦋0⦌)).app (op ⦋0⦌)) (targetVertex W H)) fy) =
          (t ≫ fullTriangle V HV fy) ≫ V.map (SimplexCategory.δ (0 : Fin 3)).op := by
      calc
        _ = (t ≫ pV) ≫ pullback.fst (endpointArrow V)
              (endpointPoint V (targetVertex V HV) fy) := by
          simpa only [Category.assoc] using congrArg (fun k ↦ t ≫ pV ≫ k)
            (transport_fst V (targetVertex_post f H) (rfl : fy = fy))
        _ = _ := by
          simpa only [Category.assoc] using congrArg (fun k ↦ t ≫ k)
            (finalEdgeFiber_edge V HV fy)
    calc
      _ = (fullTriangle W H y ≫ W.map (SimplexCategory.δ (0 : Fin 3)).op) ≫
          f.app (op ⦋1⦌) := hLeft
      _ = (fullTriangle W H y ≫ f.app (op ⦋2⦌)) ≫
          V.map (SimplexCategory.δ (0 : Fin 3)).op := by
        rw [Category.assoc, f.naturality (SimplexCategory.δ (0 : Fin 3)).op,
          ← Category.assoc]
      _ = (t ≫ fullTriangle V HV fy) ≫ V.map (SimplexCategory.δ (0 : Fin 3)).op := by
        rw [fullTriangle_post]
      _ = _ := hRight.symm
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

#print axioms targetVertex_post
#print axioms targetVertex_actual
#print axioms finalEdgeFiber_post

end
end DaggerModels.PartII.OrdinarySegalCoherentFinalFiberNaturality
