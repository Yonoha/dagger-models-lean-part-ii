import OrdinarySegalEndpointDescentAuxiliary
import SimplicialReplacementChosenHomotopyFiber

/-!
# Original endpoint simplex fibers and the auxiliary derived fibers

The source is the literal pullback of the original endpoint row at its
specified whole simplex. The comparison first applies the pointwise Kan
unit, then the checked chosen-fiber comparison. The auxiliary projection
is a fibration after its specified relative Reedy replacement. Identifying
this auxiliary construction with the original endpoint diagonal is still
a separate homotopy-colimit reconstruction obligation.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory HomotopicalAlgebra
open DaggerNativeReedyRelativeReplacement (relativeReplacement)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalEndpointDescentFiber

open OrdinaryCSSLocalization (Space)
open BisimplicialBaseSimplexFibers (Index fiber fiberDiagram)
open BisimplicialBaseSimplexKanFibers (kanFiberDiagram)
open SimplicialReplacementChosenHomotopyFiber (relativeFiber chosenFiberComparison)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev endpointArrow (W : Space) :=
  Arrow.mk (OrdinarySegalResolutionMappingFibers.endpointResolution W)

/-- The source is the original strict fiber at the whole chosen base simplex. -/
def endpointSimplexFiberComparison (W : Space) (σ : Index (endpointArrow W)) :
    fiber (endpointArrow W) σ ⟶
      relativeFiber (kanFiberDiagram (endpointArrow W)) σ :=
  (SimplicialReplacementPointwiseKan.kanUnit
    (fiberDiagram (endpointArrow W))).app σ ≫
      chosenFiberComparison (kanFiberDiagram (endpointArrow W)) σ

/-- The actual comparison retains the entire original simplex fiber weakly. -/
theorem endpointSimplexFiberComparison_weak (W : Space)
    (σ : Index (endpointArrow W)) :
    WeakEquivalence (endpointSimplexFiberComparison W σ) := by
  have : WeakEquivalence
      ((SimplicialReplacementPointwiseKan.kanUnit
        (fiberDiagram (endpointArrow W))).app σ) :=
    SimplicialReplacementPointwiseKan.kanUnit_value_weak
      (fiberDiagram (endpointArrow W)) σ
  have : WeakEquivalence
      (chosenFiberComparison (kanFiberDiagram (endpointArrow W)) σ) :=
    SimplicialReplacementChosenHomotopyFiber.chosenFiberComparison_weak
      (kanFiberDiagram (endpointArrow W)) σ
  change WeakEquivalence (_ ≫ _)
  infer_instance

/-- For the original Segal input the target is a fiber of this specified
Kan fibration; the weak comparison and fibration are supplied together. -/
theorem endpointSimplexFiberComparison_with_fibration (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (σ : Index (endpointArrow W)) :
    WeakEquivalence (endpointSimplexFiberComparison W σ) ∧
      Fibration (DaggerNativeBisimplicialDiagonal.diagonalFunctor.map
        (relativeReplacement.obj
          (OrdinarySegalEndpointDescentAuxiliary.endpointAuxiliary W)).hom) :=
  ⟨endpointSimplexFiberComparison_weak W σ,
    OrdinarySegalEndpointDescentAuxiliary.endpoint_auxiliary_relative_diagonal_fibration
      W hSegal⟩

#print axioms endpointSimplexFiberComparison_weak
#print axioms endpointSimplexFiberComparison_with_fibration

end

end DaggerModels.PartII.OrdinarySegalEndpointDescentFiber
