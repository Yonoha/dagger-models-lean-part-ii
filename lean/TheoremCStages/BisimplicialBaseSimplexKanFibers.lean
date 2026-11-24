import BisimplicialBaseSimplexFibers
import SimplicialReplacementPointwiseKan
import SimplicialReplacementRelativeDiagonalFibration

/-!
# Kan values for the actual base-simplex fiber diagram

Pullbacks over standard simplices need not themselves be Kan. The actual
fiber diagram is therefore compared, by its literal unit, with a functorial
Kan-valued diagram on the unchanged full comma category. This supplies the
auxiliary diagonal fibration, not a homotopy-colimit reconstruction theorem.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory HomotopicalAlgebra
open DaggerNativeBisimplicialHorizontalMapping (BiSSet)
open DaggerNativeReedyRelativeReplacement (relativeReplacement)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.BisimplicialBaseSimplexKanFibers

noncomputable section

open BisimplicialBaseSimplexFibers (Index fiberDiagram)
open SimplicialReplacementPointwiseKan

/-- Kan replacement of the original strict fibers, with the same comma index. -/
def kanFiberDiagram (f : Arrow BiSSet.{0}) : Index f ⥤ SSet.{0} :=
  kanDiagram (fiberDiagram f)

instance kanFiberDiagram_value_fibrant (f : Arrow BiSSet.{0}) (σ : Index f) :
    IsFibrant ((kanFiberDiagram f).obj σ) :=
  kanDiagram_value_fibrant (fiberDiagram f) σ

/-- Every original comma operator still acts weakly on the Kan-valued diagram. -/
theorem kanFiberDiagram_map_weak (f : Arrow BiSSet.{0})
    (hFib : ∀ q, Fibration (f.hom.app q))
    (hEqui : BisimplicialEquifibered.Equifibered f)
    {σ τ : Index f} (a : σ ⟶ τ) :
    WeakEquivalence ((kanFiberDiagram f).map a) :=
  kanDiagram_map_weak (fiberDiagram f)
    (by
      intro σ τ a
      exact BisimplicialBaseSimplexFibers.fiberDiagram_map_weak f hFib hEqui a) a

/-- The unit compares the two actual whole replacement diagonals weakly. -/
theorem fiberDiagram_diagonal_unit_weak (f : Arrow BiSSet.{0}) :
    WeakEquivalence
      (DaggerNativeSimplicialReplacementWeightsChange.diagonalChange
        (kanUnit (fiberDiagram f))) :=
  kanUnit_diagonal_weak (fiberDiagram f)

/-- The auxiliary arrow is the full replacement projection of the Kan fiber diagram. -/
def auxiliaryArrow (f : Arrow BiSSet.{0}) : Arrow BiSSet.{0} :=
  Arrow.mk (DaggerNativeSimplicialReplacement.projection (kanFiberDiagram f))

/-- Its actual relative Reedy replacement has a Kan-fibration diagonal. -/
theorem auxiliary_relative_diagonal_fibration (f : Arrow BiSSet.{0})
    (hFib : ∀ q, Fibration (f.hom.app q))
    (hEqui : BisimplicialEquifibered.Equifibered f) :
    Fibration (DaggerNativeBisimplicialDiagonal.diagonalFunctor.map
      (relativeReplacement.obj (auxiliaryArrow f)).hom) :=
  SimplicialReplacementRelativeDiagonalFibration.relative_diagonal_fibration
    (kanFiberDiagram f) (by
      intro σ τ a
      exact kanFiberDiagram_map_weak f hFib hEqui a)

#print axioms kanFiberDiagram_map_weak
#print axioms fiberDiagram_diagonal_unit_weak
#print axioms auxiliary_relative_diagonal_fibration

end

end DaggerModels.PartII.BisimplicialBaseSimplexKanFibers
