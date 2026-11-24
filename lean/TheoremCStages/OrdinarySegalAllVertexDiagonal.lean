import OrdinarySegalAllVertexPrecompletionFibres
import OrdinarySegalVerticalDiagonalTests
import OrdinarySegalRestrictionTargetNaturality

/-!
# The complete vertex-mapping base of the corrected vertical diagonal

The horizontal discrete mapping functor commutes with the unchanged
vertical diagonal. Applying this to the original `Fin (n + 1)` vertex set
identifies the base of the all-vertex resolution with the complete vertex
mapping space of the corrected precompletion. No endpoint-pair reduction or
replacement is used.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial
open DaggerNativeBisimplicialHorizontalMapping (BiSSet)
open DaggerNativeBisimplicialDiagonal (diagonalFunctor)

namespace DaggerModels.PartII.OrdinarySegalAllVertexDiagonal

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalVertexTupleFibres (vertices)
open HorizontalMappingVerticalDiagonal (verticalDiagonal diagramMappingDiagonalIso)

noncomputable section

/-- The native discrete mapping identification is natural in every row map. -/
def rowDiscreteMappingIso (K : SSet.{0})
    (R : SimplexCategoryᵒᵖ ⥤ Space) :
    R ⋙ diagramMappingTarget (discrete.obj K) ≅
      R ⋙ HorizontalMappingVerticalDiagonal.horizontalMappingFunctor K :=
  NatIso.ofComponents
    (fun q ↦ OrdinaryDiscreteMapping.mappingIso K (R.obj q))
    (by
      intro q r θ
      exact OrdinarySegalRestrictionTargetNaturality.mappingIso_post K (R.map θ))

/-- All original ordered vertex maps commute with the literal vertical diagonal. -/
def vertexBaseDiagonalIso (W : Space) (n : ℕ) :
    diagramMappingSpace (discrete.obj (vertices n))
        (OrdinarySegalVerticalPrecompletion.precompletion W) ≅
      diagonalFunctor.obj (OrdinarySegalAllVertexResolution.vertexBaseResolution W n) :=
  diagramMappingDiagonalIso (vertices n) (OrdinarySegalPrecompletion.resolution W) ≪≫
    (diagonalFunctor.mapIso
      (rowDiscreteMappingIso (vertices n) (OrdinarySegalPrecompletion.resolution W))).symm

/-- The original horizontal `n`-row has exactly this corrected diagonal. -/
theorem rowResolution_diagonal (W : Space) (n : ℕ) :
    diagonalFunctor.obj (OrdinarySegalResolutionMappingFibers.rowResolution W n) =
      (OrdinarySegalVerticalPrecompletion.precompletion W).obj (op ⦋n⦌) := by
  rfl

#print axioms rowDiscreteMappingIso
#print axioms vertexBaseDiagonalIso
#print axioms rowResolution_diagonal

end

end DaggerModels.PartII.OrdinarySegalAllVertexDiagonal
