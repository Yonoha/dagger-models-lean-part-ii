import OrdinarySegalWalkingEvaluation
import DaggerModelsPartII.ConstantDaggerSource

/-!
# All ordered vertices of an ordinary simplex

The constant simplicial set on `Fin (n + 1)` includes the actual ordered
vertices of the original standard simplex. Restriction along that inclusion
gives the finite-vertex map of a simplicial space. Its Kan-fibration property
uses only injective fibrancy, without a Segal or completeness assumption.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalVertexTupleFibres

open OrdinaryCSSLocalization (Space discrete)
open DaggerUnitaryDiscrete (constSSet)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- The discrete simplicial set with exactly the `n + 1` ordered vertices. -/
def vertices (n : ℕ) : SSet.{0} := constSSet (Fin (n + 1))

/-- Inclusion of every original vertex, in its given finite order. -/
def vertexInclusion (n : ℕ) : vertices n ⟶ (Δ[n] : SSet.{0}) :=
  ConstantDaggerSource.fromZero (Fin (n + 1)) (Δ[n] : SSet.{0})
    (fun i ↦ (SSet.stdSimplex.obj₀Equiv (n := n)).symm i)

/-- At degree zero the inclusion is the native standard-simplex vertex equivalence. -/
theorem vertexInclusion_zero (n : ℕ) (i : Fin (n + 1)) :
    (vertexInclusion n).app (op ⦋0⦌) i =
      (SSet.stdSimplex.obj₀Equiv (n := n)).symm i := by
  exact congrFun
    (ConstantDaggerSource.toZero_fromZero (Fin (n + 1)) (Δ[n] : SSet.{0})
      (fun j ↦ (SSet.stdSimplex.obj₀Equiv (n := n)).symm j)) i

/-- The all-vertex inclusion is degreewise injective, including when `n = 0`. -/
theorem vertexInclusion_mono (n : ℕ) : Mono (vertexInclusion n) := by
  rw [NatTrans.mono_iff_mono_app]
  intro q
  apply (mono_iff_injective _).mpr
  intro i j hij
  let α : q ⟶ op ⦋0⦌ := (SimplexCategory.const ⦋0⦌ q.unop 0).op
  have hi := congrFun ((vertexInclusion n).naturality α) i
  have hj := congrFun ((vertexInclusion n).naturality α) j
  have hzero : (vertexInclusion n).app (op ⦋0⦌) i =
      (vertexInclusion n).app (op ⦋0⦌) j := by
    calc
      _ = ((Δ[n] : SSet.{0}).map α) ((vertexInclusion n).app q i) := by
        exact hi
      _ = ((Δ[n] : SSet.{0}).map α) ((vertexInclusion n).app q j) :=
        congrArg _ hij
      _ = _ := hj.symm
  rw [vertexInclusion_zero n i, vertexInclusion_zero n j] at hzero
  exact (SSet.stdSimplex.obj₀Equiv (n := n)).symm.injective hzero

/-- Restriction of the literal horizontal simplex mapping space to all vertices. -/
def mappingVertexMap (W : Space) (n : ℕ) :
    diagramMappingSpace (discrete.obj (Δ[n] : SSet.{0})) W ⟶
      diagramMappingSpace (discrete.obj (vertices n)) W :=
  diagramMappingPrecomp (discrete.map (vertexInclusion n)) W

/-- The mapping-space all-vertex restriction is a Kan fibration. -/
theorem mappingVertexMap_fibration (W : Space) [IsFibrant W] (n : ℕ) :
    Fibration (mappingVertexMap W n) := by
  letI : Mono (vertexInclusion n) := vertexInclusion_mono n
  letI : Mono (discrete.map (vertexInclusion n)) :=
    OrdinaryCSSLocalization.discrete_map_mono _
  exact InjectiveKanDiagram.diagramMappingPrecomp_isFibration
    SimplexCategoryᵒᵖ (discrete.map (vertexInclusion n)) W

/-- The same map, with its source identified as the actual horizontal `n`-row. -/
def vertexMap (W : Space) (n : ℕ) :
    W.obj (op ⦋n⦌) ⟶ diagramMappingSpace (discrete.obj (vertices n)) W :=
  (OrdinarySegalWalkingEvaluation.simplexMappingIso W n).inv ≫
    mappingVertexMap W n

/-- Every finite-vertex row map of an injectively fibrant space is a Kan fibration. -/
theorem vertexMap_fibration (W : Space) [IsFibrant W] (n : ℕ) :
    Fibration (vertexMap W n) := by
  have : Fibration (mappingVertexMap W n) := mappingVertexMap_fibration W n
  dsimp only [vertexMap]
  infer_instance

#print axioms vertexInclusion_mono
#print axioms mappingVertexMap_fibration
#print axioms vertexMap_fibration

end

end DaggerModels.PartII.OrdinarySegalVertexTupleFibres
