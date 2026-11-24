import OrdinaryGroupoidSimplexTransitionFullyFaithful
import OrdinarySegalEndpointSquareFiberwiseRecognition
import OrdinarySegalCotensorFibrant

/-!
# Actual endpoint squares of groupoid-simplex transitions

For every original simplex operator, the whole cotensor transition has a
weak strict comparison to the pullback of the target endpoint arrow.
The comparison retains the original degree-one transition and the
source's ordered pair of degree-zero endpoints.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryGroupoidSimplexTransitionEndpointSquare

open OrdinaryCSSLocalization (Space)
open OrdinarySegalHorizontalCotensor (cotensor)
open OrdinarySegalOrderedMappingFibres (endpointArrow)
open OrdinarySegalOrderedMappingMaps (endpointMap endpoint_naturality mappingMap)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev E (k : SimplexCategory) : SSet.{0} :=
  GroupoidSimplex.parameter.obj k

/-- The literal comparison for the original transition's ordered endpoint
square, using the same degree-one and degree-zero maps. -/
def endpointComparison {n m : SimplexCategory} (θ : n ⟶ m) (W : Space) :
    (cotensor (E m) W).obj (op ⦋1⦌) ⟶
      pullback (endpointArrow (cotensor (E n) W))
        (endpointMap
          (OrdinaryGroupoidSimplexCotensorTransitionHomotopy.transition θ W)) :=
  pullback.lift
    ((OrdinaryGroupoidSimplexCotensorTransitionHomotopy.transition θ W).app (op ⦋1⦌))
    (endpointArrow (cotensor (E m) W))
    (endpoint_naturality
      (OrdinaryGroupoidSimplexCotensorTransitionHomotopy.transition θ W)).symm

/-- All ordered-fiber weak equivalences recognize the actual
homotopy-cartesian endpoint comparison for this transition. -/
theorem endpointComparison_weak {n m : SimplexCategory} (θ : n ⟶ m)
    (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) :
    WeakEquivalence (endpointComparison θ W) := by
  let X := cotensor (E m) W
  let Y := cotensor (E n) W
  let t := OrdinaryGroupoidSimplexCotensorTransitionHomotopy.transition θ W
  have : IsFibrant X :=
    OrdinarySegalCotensorFibrant.cotensor_injectiveFibrant (E m) W inferInstance
  have : IsFibrant Y :=
    OrdinarySegalCotensorFibrant.cotensor_injectiveFibrant (E n) W inferInstance
  have hf : ∀ x y : (X.obj (op ⦋0⦌)).obj (op ⦋0⦌),
      WeakEquivalence (mappingMap t x y) := by
    intro x y
    exact OrdinaryGroupoidSimplexTransitionFullyFaithful.mappingMap_weak
      θ W hSegal x y
  change WeakEquivalence
    (OrdinarySegalEndpointSquareFiberwiseRecognition.comparison t)
  exact OrdinarySegalEndpointSquareFiberwiseRecognition.comparison_weak_of_mappingMap_weak
    t hf

#print axioms endpointComparison
#print axioms endpointComparison_weak

end
end DaggerModels.PartII.OrdinaryGroupoidSimplexTransitionEndpointSquare
