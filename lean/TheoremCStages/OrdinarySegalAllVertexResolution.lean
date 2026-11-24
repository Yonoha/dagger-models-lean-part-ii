import OrdinaryAllVertexSquareComparison
import OrdinarySegalResolutionMappingFibers
import OrdinarySegalRestrictionTargetNaturality
import BisimplicialEquifibered

/-!
# The actual all-vertex resolution is equifibered in every dimension

The horizontal degree remains fixed while the original groupoid-simplex
parameter varies. Every whole original simplex is restricted to its full
ordered vertex tuple. No replacement Segal or completeness assertion is made.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerNativeBisimplicialHorizontalMapping (BiSSet)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalAllVertexResolution

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalVertexTupleFibres (vertices vertexMap mappingVertexMap)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- The original representable mapping object is naturally the actual row. -/
def simplexEvaluationIso (n : ℕ) :
    diagramMappingTarget (discrete.obj (Δ[n] : SSet.{0})) ≅
      (evaluation SimplexCategoryᵒᵖ SSet.{0}).obj (op ⦋n⦌) :=
  NatIso.ofComponents (fun W ↦ OrdinarySegalWalkingEvaluation.simplexMappingIso W n)
    (by intro W Z f; exact OrdinarySegalRestrictionTargetNaturality.simplexMappingIso_post f n)

/-- Restricting to all vertices commutes with each complete target map. -/
def mappingVertexRestriction (n : ℕ) :
    diagramMappingTarget (discrete.obj (Δ[n] : SSet.{0})) ⟶
      diagramMappingTarget (discrete.obj (vertices n)) where
  app W := mappingVertexMap W n
  naturality {_ _} f := by
    apply NatTrans.ext
    funext q x
    rfl

/-- All ordered vertices, as a natural transformation of the actual horizontal row. -/
def vertexRestriction (n : ℕ) :
    (evaluation SimplexCategoryᵒᵖ SSet.{0}).obj (op ⦋n⦌) ⟶
      diagramMappingTarget (discrete.obj (vertices n)) :=
  (simplexEvaluationIso n).inv ≫ mappingVertexRestriction n

/-- The original full tuple-mapping base in every groupoid-simplex parameter. -/
def vertexBaseResolution (W : Space) (n : ℕ) : BiSSet.{0} :=
  OrdinarySegalPrecompletion.resolution W ⋙
    diagramMappingTarget (discrete.obj (vertices n))

/-- The actual whole simplex-to-vertices arrow before taking its vertical diagonal. -/
def vertexResolution (W : Space) (n : ℕ) :
    OrdinarySegalResolutionMappingFibers.rowResolution W n ⟶ vertexBaseResolution W n :=
  Functor.whiskerLeft (OrdinarySegalPrecompletion.resolution W) (vertexRestriction n)

/-- Every original row of the full tuple resolution is a Kan fibration. -/
theorem vertexResolution_row_fibration (W : Space) [IsFibrant W] (n : ℕ)
    (q : SimplexCategoryᵒᵖ) : Fibration ((vertexResolution W n).app q) := by
  have : IsFibrant ((OrdinarySegalPrecompletion.resolution W).obj q) :=
    OrdinarySegalCotensorFibrant.cotensor_injectiveFibrant
      (GroupoidSimplex.parameter.obj q.unop) W inferInstance
  exact OrdinarySegalVertexTupleFibres.vertexMap_fibration
    ((OrdinarySegalPrecompletion.resolution W).obj q) n

/-- All actual tuple transition squares are weak pullback comparisons. -/
theorem vertexResolution_equifibered (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) (n : ℕ) :
    BisimplicialEquifibered.Equifibered (Arrow.mk (vertexResolution W n)) := by
  intro q r θ
  change WeakEquivalence (OrdinaryAllVertexSquareComparison.vertexComparison
    (OrdinaryGroupoidSimplexCotensorTransitionHomotopy.transition θ.unop W) n)
  exact OrdinaryAllVertexSquareComparison.transition_vertexComparison_weak θ.unop W hSegal n

#print axioms vertexResolution
#print axioms vertexResolution_row_fibration
#print axioms vertexResolution_equifibered

end

end DaggerModels.PartII.OrdinarySegalAllVertexResolution
