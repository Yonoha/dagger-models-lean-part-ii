import OrdinarySegalRestrictionZeroCalibration
import OrdinarySegalCoherentFixedTriangleSource
import OrdinaryWalkingCoherentVertexCalibration

/-!
# The coherent row edge has the original whole-map object endpoints

The row source is `d1` and the row target is `d0`. They coincide with the
two original groupoid vertices of the same actual row-zero coherent map,
transported into the zero-simplex restriction by its existing isomorphism.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySegalCoherentActualEndpoints

open OrdinaryCSSLocalization (Space)
open OrdinarySegalCoherentFixedHornSourceIso (coherentRowEdge)
open OrdinarySegalCoherentFixedTriangleSource (sourceVertex)

noncomputable section

private abbrev E : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌

/-- Both ordered faces of the coherent edge retain the original groupoid vertices. -/
theorem vertex_actual (W : Space) (H : E ⟶ W.flip.obj (op ⦋0⦌)) (i : Fin 2) :
    SSet.yonedaEquiv
        (coherentRowEdge W (H ≫ (diagramRestrictionSimplexIso W.flip 0).inv) ≫
          W.map (SimplexCategory.δ i.rev).op) =
      SSet.yonedaEquiv (JTParameterContraction.parameterVertex ⦋1⦌ i ≫ H) := by
  have hδ : SimplexCategory.δ i.rev = SimplexCategory.const ⦋0⦌ ⦋1⦌ i := by
    fin_cases i <;> ext j <;> fin_cases j <;> rfl
  change (W.flip.obj (op ⦋0⦌)).map (SimplexCategory.δ i.rev).op
      (SSet.yonedaEquiv (X := W.obj (op ⦋1⦌)) (n := ⦋0⦌)
        (coherentRowEdge W (H ≫ (diagramRestrictionSimplexIso W.flip 0).inv))) = _
  rw [OrdinarySegalRestrictionZeroCalibration.coherentRowEdge_actual,
    ← SSet.yonedaEquiv_map_comp, ← Category.assoc, hδ,
    OrdinaryWalkingCoherentVertexCalibration.simplexUnit_vertex]

/-- The source used by the original ordered-fiber projection is the
same original time-zero object of the whole coherent arrow. -/
theorem sourceVertex_actual (W : Space) (H : E ⟶ W.flip.obj (op ⦋0⦌)) :
    sourceVertex W (H ≫ (diagramRestrictionSimplexIso W.flip 0).inv) =
      SSet.yonedaEquiv (JTParameterContraction.parameterVertex ⦋1⦌ 0 ≫ H) :=
  vertex_actual W H 0

#print axioms vertex_actual
#print axioms sourceVertex_actual

end
end DaggerModels.PartII.OrdinarySegalCoherentActualEndpoints
