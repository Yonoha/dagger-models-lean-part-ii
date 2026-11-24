import BisimplicialCommaDiagonalReconstruction
import BisimplicialBaseSimplexKanFibers
import NativeSimplexIndexResolution
import SimplicialReplacementChosenHomotopyFiber

/-!
# The parameter bar over the unchanged comma index

Every value of the parameter diagram is its original whole standard
simplex. Its complete replacement therefore projects weakly to the
nerve of the comma index. The two further projection triangles retain
the exact fiber and pointwise Kan-unit maps.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open MonoidalCategory CartesianMonoidalCategory
open DaggerSSetGluing DaggerOriginalProductGadget
open DaggerOriginalCounitBNextConeEvaluationIndex
open DaggerOriginalCounitRightConeQRealizationAdjunction
open DaggerNativeBisimplicialHorizontalMapping (BiSSet)
open DaggerNativeSimplicialReplacement (replacement diagonalProjection)
open DaggerNativeSimplicialReplacementWeightsChange (diagonalChange)
open DaggerSimplicialReplacementChosenFiber (chainPoint diagonalInclusion)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.BisimplicialCommaParameterProjection

open BisimplicialBaseSimplexFibers (Index fiberDiagram simplexProjection)
open BisimplicialBaseSimplexKanFibers (kanFiberDiagram)
open BisimplicialCommaDiagonalReconstruction (parameterDiagram)

noncomputable section

variable (f : Arrow BiSSet.{0})

/-- The original full standard simplex at every comma object is weakly
contractible, with no hypothesis on either bisimplicial object. -/
theorem parameter_point_GW (σ : Index f) :
    GW (pointMap ((parameterDiagram f).obj σ)) := by
  let Y := (parameterDiagram f).obj σ
  let e := pointIsTerminal.{0}.uniqueUpToIso (isTerminalTensorUnit (C := SSet.{0}))
  have : IsIso e.inv := e.isIso_inv
  have : WeakEquivalence (toUnit Y) := (weakEquivalence_iff_GW _).mpr
    (DaggerActualKanSimplexCotensorComparison.simplex_toUnit_GW σ.left.len)
  have he : toUnit Y ≫ e.inv = pointMap Y := pointIsTerminal.hom_ext _ _
  apply (weakEquivalence_iff_GW _).mp
  rw [← he]
  infer_instance

/-- The complete parameter bar projects weakly to the actual nerve
of the full comma index. -/
theorem parameterProjection_weak :
    WeakEquivalence (diagonalProjection (parameterDiagram f)) :=
  (weakEquivalence_iff_GW _).mpr
    (DaggerNativeSimplicialReplacement.diagonalProjection_GW
      (parameterDiagram f) (parameter_point_GW f))

/-- Forgetting the strict-fiber coordinate leaves exactly the same
complete chain in the comma index. -/
theorem simplexProjection_projection_triangle :
    diagonalChange (simplexProjection f) ≫ diagonalProjection (parameterDiagram f) =
      diagonalProjection (fiberDiagram f) :=
  DaggerNativeSimplicialReplacementWeightsChange.projection_square (simplexProjection f)

/-- The pointwise Kan unit also leaves the complete comma chain fixed. -/
theorem kanUnit_projection_triangle :
    diagonalChange (SimplicialReplacementPointwiseKan.kanUnit (fiberDiagram f)) ≫
        diagonalProjection (kanFiberDiagram f) =
      diagonalProjection (fiberDiagram f) :=
  DaggerNativeSimplicialReplacementWeightsChange.projection_square
    (SimplicialReplacementPointwiseKan.kanUnit (fiberDiagram f))

/-- A literal zero-simplex of one original base row, retained as an
object of the unchanged full comma index. -/
def zeroSimplexIndex (q : SimplexCategoryᵒᵖ)
    (b : (Δ[0] : SSet.{0}) ⟶ f.right.obj q) : Index f where
  left := ⦋0⦌
  right := q
  hom := b

/-- Insert the entire zero-simplex parameter at the constant comma chain. -/
def zeroSimplexParameterPoint (q : SimplexCategoryᵒᵖ)
    (b : (Δ[0] : SSet.{0}) ⟶ f.right.obj q) :
    (Δ[0] : SSet.{0}) ⟶
      DaggerBisimplicialDiagonal.diag (replacement (parameterDiagram f)) :=
  diagonalInclusion (parameterDiagram f) (zeroSimplexIndex f q b)

/-- The parameter point has exactly the selected comma object as its
projection; no endpoint or vertex is replaced. -/
theorem zeroSimplexParameterPoint_projection (q : SimplexCategoryᵒᵖ)
    (b : (Δ[0] : SSet.{0}) ⟶ f.right.obj q) :
    zeroSimplexParameterPoint f q b ≫ diagonalProjection (parameterDiagram f) =
      chainPoint (zeroSimplexIndex f q b) := by
  apply NatTrans.ext
  funext r x
  rfl

#print axioms parameter_point_GW
#print axioms parameterProjection_weak
#print axioms simplexProjection_projection_triangle
#print axioms kanUnit_projection_triangle
#print axioms zeroSimplexParameterPoint_projection

end

end DaggerModels.PartII.BisimplicialCommaParameterProjection
