import OrdinaryWalkingCoherentContraction
import DaggerModelsPartII.JTParameterVertexKan
import TopCatModelCategory.SSet.Monoidal

/-!
# Calibrating groupoid-time slices at the original vertices

The constant-at-vertex map factors through the actual parameter vertex.
Consequently the two tensor slices used by the coherent contraction are
the original right-unitor vertex slices. The checked simplex-unit vertex
equation identifies those same vertices with the directed edge.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial MonoidalCategory
open CartesianMonoidalCategory
open DaggerOriginalCodiscreteNerveInjective

namespace DaggerModels.PartII.OrdinaryWalkingCoherentVertexCalibration

noncomputable section

private abbrev E : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌

private theorem constant_vertex_map (i : Fin 2) :
    mapOfVertices E (fun _ => i) =
      SSet.stdSimplex.isTerminalObj₀.from E ≫
        mapOfVertices (Δ[0] : SSet.{0}) (fun _ => i) := by
  apply NatTrans.ext
  funext q x
  apply nerve.ext_of_isThin
  funext a
  apply Codiscrete.ext
  rfl

/-- The actual constant parameter map factors through its original vertex. -/
theorem constantAt_vertex (i : Fin 2) :
    JTParameterContraction.constantAt ⦋1⦌ i =
      SSet.stdSimplex.isTerminalObj₀.from E ≫
        JTParameterContraction.parameterVertex ⦋1⦌ i := by
  dsimp only [JTParameterContraction.constantAt,
    JTParameterContraction.parameterVertex]
  rw [constant_vertex_map, Category.assoc]

/-- The exact contraction slice is the right-unitor inclusion of the
original groupoid-parameter vertex. -/
theorem slice_vertex (i : Fin 2) :
    OrdinaryWalkingCoherentContraction.slice i =
      (SSet.stdSimplex.rightUnitor E).inv ≫
        E ◁ JTParameterContraction.parameterVertex ⦋1⦌ i := by
  apply NatTrans.ext
  funext q x
  apply Prod.ext
  · rfl
  · have h := congrFun (NatTrans.congr_app (constantAt_vertex i) q) x
    exact h

/-- The vertex is also the original directed simplex-unit vertex. -/
theorem simplexUnit_vertex (i : Fin 2) :
    SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ i) ≫
        JTCylinderCEComparison.simplexUnit.app ⦋1⦌ =
      JTParameterContraction.parameterVertex ⦋1⦌ i :=
  JTParameterVertexKan.simplexUnit_vertex ⦋1⦌ i

#print axioms constantAt_vertex
#print axioms slice_vertex
#print axioms simplexUnit_vertex

end
end DaggerModels.PartII.OrdinaryWalkingCoherentVertexCalibration
