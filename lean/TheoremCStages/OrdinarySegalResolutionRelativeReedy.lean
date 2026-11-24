import OrdinarySegalResolutionMappingFibers
import OrdinarySegalCotensorFibrant
import NativeRelativeReedyFibreComparisonWeak

/-!
# Relative Reedy comparison for the actual endpoint resolution

The original endpoint map in every outer row is a Kan fibration. The
existing relative Reedy fiber theorem therefore applies to the actual
compatible point section. Its conclusion compares strict diagonal fibers;
it does not assert that the replacement diagonal is a Kan fibration or
that either strict diagonal fiber is a derived fiber.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalResolutionRelativeReedy

open OrdinaryCSSLocalization (Space)
open OrdinarySegalResolutionMappingFibers
open OrdinarySegalOrderedMappingFibres (endpointArrow)
open DaggerNativeBisimplicialDiagonal (diagonalFunctor)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- The chosen-product coordinate change preserves the original Kan
fibration in every outer groupoid-simplex row. -/
theorem endpointResolution_row_fibration (W : Space) [IsFibrant W]
    (q : SimplexCategoryᵒᵖ) : Fibration ((endpointResolution W).app q) := by
  let V := (OrdinarySegalPrecompletion.resolution W).obj q
  have : IsFibrant V :=
    OrdinarySegalCotensorFibrant.cotensor_injectiveFibrant
      (GroupoidSimplex.parameter.obj q.unop) W inferInstance
  have : Fibration (endpointArrow V) :=
    OrdinarySegalOrderedMappingFibres.endpointArrow_fibration V
  have h : (endpointResolution W).app q =
      endpointArrow V ≫ (rowBaseIso W q).inv := by
    calc
      _ = ((endpointResolution W).app q ≫ (rowBaseIso W q).hom) ≫
          (rowBaseIso W q).inv := by simp
      _ = _ := congrArg (fun k ↦ k ≫ (rowBaseIso W q).inv)
        (endpointResolution_app W q)
  rw [h]
  infer_instance

/-- The retained relative Reedy theorem gives the actual strict diagonal
fiber comparison, at precisely the original constant-section point pair. -/
theorem diagonalComparison_weak (W : Space) [IsFibrant W]
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    WeakEquivalence
      (DaggerNativeRelativeReedyBisimplicialFibres.imageComparison diagonalFunctor
        (Arrow.mk (endpointResolution W)) (pointResolution W x y)) :=
  DaggerNativeRelativeReedyFibreComparisonWeak.diagonalComparison_weak
    (Arrow.mk (endpointResolution W)) (endpointResolution_row_fibration W)
    (pointResolution W x y)

#print axioms endpointResolution_row_fibration
#print axioms diagonalComparison_weak

end
end DaggerModels.PartII.OrdinarySegalResolutionRelativeReedy
