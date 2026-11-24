import OrdinarySegalAllVertexUnitFibres
import OrdinarySegalAllVertexResolution
import OrdinarySegalVerticalPrecompletionFiberComparison

/-!
# Full vertex tuples in the corrected vertical precompletion resolution

The original complete vertex restriction of each outer resolution row is
identified with the previously checked horizontal `vertexMap`. The same
row uses the exact constant section whose diagonal is the corrected unit.
The weak rowwise strict-fiber base change is retained for any tuple point.
Identification of the diagonal of these row fibers with the direct strict
fiber of the corrected precompletion is a separate coherence step.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalAllVertexPrecompletionFibres

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalVertexTupleFibres (vertices vertexMap)
open OrdinarySegalHorizontalCotensorPoint (constantSection)
open OrdinaryAllVertexSquareComparison (vertexComparison)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- The all-vertex arrow of an outer row is the original vertex restriction. -/
theorem vertexResolution_app (W : Space) (n : ℕ) (q : SimplexCategoryᵒᵖ) :
    (OrdinarySegalAllVertexResolution.vertexResolution W n).app q =
      vertexMap ((OrdinarySegalPrecompletion.resolution W).obj q) n := by
  rfl

/-- At the same indices, the original outer resolution unit is the constant section. -/
theorem resolutionUnit_app (W : Space) (q : SimplexCategoryᵒᵖ) :
    (OrdinarySegalPrecompletion.resolutionUnit W).app q =
      constantSection (GroupoidSimplex.parameter.obj q.unop) W := by
  rfl

/-- The all-vertex square of each original outer unit row is weak. -/
theorem resolutionUnit_vertexComparison_weak (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (n : ℕ) (q : SimplexCategoryᵒᵖ) :
    WeakEquivalence (vertexComparison
      ((OrdinarySegalPrecompletion.resolutionUnit W).app q) n) := by
  rw [resolutionUnit_app]
  exact OrdinarySegalAllVertexUnitFibres.constantSection_vertexComparison_weak
    W hSegal q.unop n

/-- The actual tuple-point fiber comparison in every outer row is weak. -/
theorem resolutionUnit_strictTupleComparison_weak (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (n : ℕ) (q : SimplexCategoryᵒᵖ)
    (b : (Δ[0] : SSet.{0}) ⟶ diagramMappingSpace (discrete.obj (vertices n)) W) :
    WeakEquivalence
      (OrdinarySegalAllVertexUnitFibres.strictTupleComparison W q.unop n b) :=
  OrdinarySegalAllVertexUnitFibres.strictTupleComparison_weak W hSegal q.unop n b

/-- The diagonal row-unit component is exactly the corrected unit at all
three original indices: horizontal `n`, outer `q`, and inner `q`. -/
theorem rowUnit_diagonal (W : Space) (n : ℕ) (q : SimplexCategoryᵒᵖ) :
    ((OrdinarySegalResolutionMappingFibers.rowUnit W n).app q).app q =
      ((OrdinarySegalVerticalPrecompletion.unit W).app (op ⦋n⦌)).app q := by
  exact (OrdinarySegalVerticalPrecompletion.unit_app_app W (op ⦋n⦌) q).symm

#print axioms vertexResolution_app
#print axioms resolutionUnit_vertexComparison_weak
#print axioms rowUnit_diagonal

end

end DaggerModels.PartII.OrdinarySegalAllVertexPrecompletionFibres
