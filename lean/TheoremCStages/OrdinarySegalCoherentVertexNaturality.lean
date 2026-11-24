import OrdinarySegalCoherentFixedEdgeNaturality
import OrdinarySegalCoherentFixedTriangleSource

/-!
# Whole target maps preserve the original ordered coherent-edge vertices

Both faces retain their literal order. The resulting equality identifies
the source of the transformed coherent edge with the actual row-zero image,
as needed for the original endpoint-dependent mapping-fiber square.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySegalCoherentVertexNaturality

open OrdinaryCSSLocalization (Space)
open OrdinarySegalCoherentFixedHornSourceIso (coherentRowEdge)
open OrdinarySegalCoherentFixedTriangleSource (sourceVertex)
open OrdinarySegalCoherentFixedEdgeNaturality (postCoherent)

noncomputable section

private abbrev E : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌

/-- Each original ordered face transforms by the actual degree-zero map. -/
theorem vertex_post {W V : Space} (f : W ⟶ V)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) (i : Fin 2) :
    SSet.yonedaEquiv
        (coherentRowEdge V (postCoherent f H) ≫ V.map (SimplexCategory.δ i.rev).op) =
      ((f.app (op ⦋0⦌)).app (op ⦋0⦌))
        (SSet.yonedaEquiv (coherentRowEdge W H ≫ W.map (SimplexCategory.δ i.rev).op)) := by
  dsimp only [postCoherent]
  rw [← OrdinarySegalCoherentEdgeNaturality.coherentRowEdge_post,
    Category.assoc, ← f.naturality (SimplexCategory.δ i.rev).op,
    ← Category.assoc, SSet.yonedaEquiv_comp]

/-- The transformed coherent source is the actual image of the same original source. -/
theorem sourceVertex_post {W V : Space} (f : W ⟶ V)
    (H : E ⟶ diagramRestriction (Δ[0] : SSet.{0}) W.flip) :
    sourceVertex V (postCoherent f H) =
      ((f.app (op ⦋0⦌)).app (op ⦋0⦌)) (sourceVertex W H) :=
  vertex_post f H 0

#print axioms vertex_post
#print axioms sourceVertex_post

end
end DaggerModels.PartII.OrdinarySegalCoherentVertexNaturality
