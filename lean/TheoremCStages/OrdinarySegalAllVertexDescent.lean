import OrdinarySegalAllVertexResolution
import BisimplicialCommaZeroFiberComparison
import SimplicialReplacementChosenHomotopyFiber

/-!
# The checked comma-descent construction at every original vertex tuple

These are the actual all-vertex arrows of the groupoid-simplex resolution,
not arbitrary replacements. The source fibers and both unit maps are kept.
Segal recognition after replacement and completeness are still separate.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerNativeBisimplicialHorizontalMapping (BiSSet)
open DaggerNativeBisimplicialDiagonal (diagonalFunctor)
open DaggerNativeReedyRelativeReplacement (relativeReplacement)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalAllVertexDescent

open OrdinaryCSSLocalization (Space)
open BisimplicialBaseSimplexFibers (Index fiber fiberDiagram)
open BisimplicialBaseSimplexKanFibers (kanFiberDiagram)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- The unchanged full all-vertex arrow in the original outer parameter. -/
def vertexArrow (W : Space) (n : ℕ) : Arrow BiSSet.{0} :=
  Arrow.mk (OrdinarySegalAllVertexResolution.vertexResolution W n)

/-- The original full comma auxiliary projection, at this actual tuple arrow. -/
def auxiliary (W : Space) (n : ℕ) : Arrow BiSSet.{0} :=
  BisimplicialBaseSimplexKanFibers.auxiliaryArrow (vertexArrow W n)

/-- The actual relative auxiliary diagonal is a Kan fibration in every dimension. -/
theorem auxiliary_relative_diagonal_fibration (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) (n : ℕ) :
    Fibration (diagonalFunctor.map (relativeReplacement.obj (auxiliary W n)).hom) :=
  BisimplicialBaseSimplexKanFibers.auxiliary_relative_diagonal_fibration
    (vertexArrow W n)
    (OrdinarySegalAllVertexResolution.vertexResolution_row_fibration W n)
    (OrdinarySegalAllVertexResolution.vertexResolution_equifibered W hSegal n)

/-- The whole original tuple-simplex fiber enters the actual relative auxiliary fiber. -/
def simplexFiberComparison (W : Space) (n : ℕ) (σ : Index (vertexArrow W n)) :
    fiber (vertexArrow W n) σ ⟶
      SimplicialReplacementChosenHomotopyFiber.relativeFiber
        (kanFiberDiagram (vertexArrow W n)) σ :=
  (SimplicialReplacementPointwiseKan.kanUnit (fiberDiagram (vertexArrow W n))).app σ ≫
    SimplicialReplacementChosenHomotopyFiber.chosenFiberComparison
      (kanFiberDiagram (vertexArrow W n)) σ

/-- The actual simplex-fiber comparison retains the full original value weakly. -/
theorem simplexFiberComparison_weak (W : Space) (n : ℕ)
    (σ : Index (vertexArrow W n)) : WeakEquivalence (simplexFiberComparison W n σ) := by
  have : WeakEquivalence
      ((SimplicialReplacementPointwiseKan.kanUnit (fiberDiagram (vertexArrow W n))).app σ) :=
    SimplicialReplacementPointwiseKan.kanUnit_value_weak _ _
  have : WeakEquivalence
      (SimplicialReplacementChosenHomotopyFiber.chosenFiberComparison
        (kanFiberDiagram (vertexArrow W n)) σ) :=
    SimplicialReplacementChosenHomotopyFiber.chosenFiberComparison_weak _ _
  change WeakEquivalence (_ ≫ _)
  infer_instance

/-- At any actual original zero simplex, the canonical tuple-fiber inclusion
into the chosen bar fiber is weak, with its original point retained. -/
theorem zeroFiberToChosen_weak (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) (n : ℕ)
    (q : SimplexCategoryᵒᵖ)
    (b : (Δ[0] : SSet.{0}) ⟶ (vertexArrow W n).right.obj q) :
    WeakEquivalence
      (BisimplicialCommaZeroFiberComparison.zeroFiberToChosen (vertexArrow W n) q b) :=
  BisimplicialCommaZeroFiberComparison.zeroFiberToChosen_weak (vertexArrow W n) q b
    (OrdinarySegalAllVertexResolution.vertexResolution_row_fibration W n)
    (OrdinarySegalAllVertexResolution.vertexResolution_equifibered W hSegal n)

#print axioms auxiliary_relative_diagonal_fibration
#print axioms simplexFiberComparison_weak
#print axioms zeroFiberToChosen_weak

end

end DaggerModels.PartII.OrdinarySegalAllVertexDescent
