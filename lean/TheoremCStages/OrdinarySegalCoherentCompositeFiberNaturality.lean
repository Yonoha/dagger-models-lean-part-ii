import OrdinarySegalCoherentFixedTriangleNaturality
import OrdinarySegalCoherentVertexNaturality
import OrdinarySegalOrderedMappingTransportCoordinates
import OrdinarySegalCoherentFixedTriangleSourceCoordinates

/-!
# The original composite-fiber projection is natural with its actual endpoints

The transformed source vertex is transported by its proved equality with
the original row-zero image. Both vertical fiber maps are the original
`mappingMap`, and the center map retains the whole fixed triangle.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySegalCoherentCompositeFiberNaturality

open OrdinaryCSSLocalization (Space)
open OrdinarySegalOrderedMappingFibres (endpointArrow endpointPoint)
open OrdinarySegalOrderedMappingMaps (mappingMap mappingMap_fst)
open OrdinarySegalOrderedMappingEndpointTransport (transport)
open OrdinarySegalOrderedMappingTransportCoordinates (transport_fst)
open OrdinarySegalCoherentFixedTriangle (fullTriangle)
open OrdinarySegalCoherentFixedTriangleSource (sourceVertex compositeToOriginalFiber)
open OrdinarySegalCoherentFixedTriangleSourceCoordinates (compositeToOriginalFiber_fst)
open OrdinarySegalCoherentFixedEdgeNaturality (postCoherent)
open OrdinarySegalCoherentFixedTriangleNaturality (fixedTriangleMap fullTriangle_post)
open OrdinarySegalCoherentVertexNaturality (sourceVertex_post)

noncomputable section

private abbrev E : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌

/-- The commuting square keeps the literal original mapping-fiber map,
with only the explicit equality transport of the transformed coherent source. -/
theorem compositeToOriginalFiber_post {W V : Space} (f : W ⟶ V)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip)
    (y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    compositeToOriginalFiber W H y ≫ mappingMap f (sourceVertex W H) y =
      fixedTriangleMap f H y ≫
        compositeToOriginalFiber V (postCoherent f H)
          (((f.app (op ⦋0⦌)).app (op ⦋0⦌)) y) ≫
            transport V (sourceVertex_post f H) rfl := by
  let HV := postCoherent f H
  let fy := ((f.app (op ⦋0⦌)).app (op ⦋0⦌)) y
  let pW := compositeToOriginalFiber W H y
  let pV := compositeToOriginalFiber V HV fy
  let t := fixedTriangleMap f H y
  let c := transport V (sourceVertex_post f H) (rfl : fy = fy)
  change pW ≫ mappingMap f (sourceVertex W H) y = t ≫ pV ≫ c
  apply pullback.hom_ext
  · have hLeft :
        (pW ≫ mappingMap f (sourceVertex W H) y) ≫
            pullback.fst (endpointArrow V)
              (endpointPoint V
                (((f.app (op ⦋0⦌)).app (op ⦋0⦌)) (sourceVertex W H)) fy) =
          (fullTriangle W H y ≫ W.map (SimplexCategory.δ (1 : Fin 3)).op) ≫
            f.app (op ⦋1⦌) := by
      calc
        _ = (pW ≫ pullback.fst (endpointArrow W)
              (endpointPoint W (sourceVertex W H) y)) ≫ f.app (op ⦋1⦌) := by
          simpa only [Category.assoc] using congrArg (fun k ↦ pW ≫ k)
            (mappingMap_fst f (sourceVertex W H) y)
        _ = _ := by rw [compositeToOriginalFiber_fst]
    have hRight :
        (t ≫ pV ≫ c) ≫ pullback.fst (endpointArrow V)
            (endpointPoint V
              (((f.app (op ⦋0⦌)).app (op ⦋0⦌)) (sourceVertex W H)) fy) =
          (t ≫ fullTriangle V HV fy) ≫ V.map (SimplexCategory.δ (1 : Fin 3)).op := by
      calc
        _ = (t ≫ pV) ≫ pullback.fst (endpointArrow V)
              (endpointPoint V (sourceVertex V HV) fy) := by
          simpa only [Category.assoc] using congrArg (fun k ↦ t ≫ pV ≫ k)
            (transport_fst V (sourceVertex_post f H) (rfl : fy = fy))
        _ = _ := by
          simpa only [Category.assoc] using congrArg (fun k ↦ t ≫ k)
            (compositeToOriginalFiber_fst V HV fy)
    calc
      _ = (fullTriangle W H y ≫ W.map (SimplexCategory.δ (1 : Fin 3)).op) ≫
          f.app (op ⦋1⦌) := hLeft
      _ = (fullTriangle W H y ≫ f.app (op ⦋2⦌)) ≫
          V.map (SimplexCategory.δ (1 : Fin 3)).op := by
        rw [Category.assoc, f.naturality (SimplexCategory.δ (1 : Fin 3)).op,
          ← Category.assoc]
      _ = (t ≫ fullTriangle V HV fy) ≫ V.map (SimplexCategory.δ (1 : Fin 3)).op := by
        rw [fullTriangle_post]
      _ = _ := hRight.symm
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

#print axioms compositeToOriginalFiber_post

end
end DaggerModels.PartII.OrdinarySegalCoherentCompositeFiberNaturality
