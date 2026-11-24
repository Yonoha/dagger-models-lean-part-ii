import BisimplicialCommaColumnDeformation
import SimplicialReplacementColumnElements
import NativeBisimplicialDiagonal
import OriginalDiagonalGeometricReconciledRecovered

/-!
# Reconstruction from the full comma fiber bar to the original row bar

Forgetting the standard-simplex parameter gives the actual full change-and-
reindex map. Its columns are the nerves of the explicit Elements deformation
retractions. This compares two full bars; a comparison from the row bar to
the original bisimplicial diagonal is still separate.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerNativeBisimplicialHorizontalMapping (BiSSet)
open DaggerNativeBisimplicialDiagonal (diagonalFunctor)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.BisimplicialCommaBarReconstruction

open BisimplicialBaseSimplexFibers (fiberDiagram totalProjection)
open SimplicialReplacementColumnElements

noncomputable section

/-- The original total-row projection acts on each entire replacement cell. -/
def totalBarMap (f : Arrow BiSSet.{0}) :
    DaggerNativeSimplicialReplacement.replacement (fiberDiagram f) ⟶
      DaggerNativeSimplicialReplacement.replacement f.left :=
  replacementMap (Comma.snd SSet.stdSimplex f.right)
    (fiberDiagram f) f.left (totalProjection f)

/-- On column Elements the same actual map is the original forget functor. -/
theorem elementMap_forget (f : Arrow BiSSet.{0}) (k : SimplexCategoryᵒᵖ) :
    elementMap (Comma.snd SSet.stdSimplex f.right)
      (fiberDiagram f) f.left (totalProjection f) k =
      BisimplicialCommaColumnRetraction.forget f k := by
  refine CategoryTheory.Functor.hext (fun _ ↦ rfl) ?_
  intro P Q a
  rfl

/-- Both exact column isomorphisms intertwine the complete original maps. -/
theorem totalBarMap_column_triangle (f : Arrow BiSSet.{0})
    (k : SimplexCategoryᵒᵖ) :
    (columnIso (fiberDiagram f) k).hom ≫
        nerveMap (BisimplicialCommaColumnRetraction.forget f k) =
      (((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type 0)).map
        (totalBarMap f)).app k) ≫ (columnIso f.left k).hom := by
  have h := column_triangle (Comma.snd SSet.stdSimplex f.right)
    (fiberDiagram f) f.left (totalProjection f) k
  rw [elementMap_forget] at h
  exact h

/-- Every column comparison is weak, without row fibrations or Kan values. -/
theorem totalBarMap_column_weak (f : Arrow BiSSet.{0})
    (k : SimplexCategoryᵒᵖ) :
    WeakEquivalence (C := SSet.{0})
      (((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type 0)).map
        (totalBarMap f)).app k) := by
  have : WeakEquivalence (C := SSet.{0})
      (nerveMap (BisimplicialCommaColumnRetraction.forget f k)) :=
    BisimplicialCommaColumnDeformation.nerve_forget_weak f k
  have hc : WeakEquivalence (C := SSet.{0})
      ((((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type 0)).map
        (totalBarMap f)).app k) ≫ (columnIso f.left k).hom) := by
    rw [← totalBarMap_column_triangle]
    infer_instance
  have : WeakEquivalence (C := SSet.{0})
      ((((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type 0)).map
        (totalBarMap f)).app k) ≫ (columnIso f.left k).hom) := hc
  exact weakEquivalence_of_postcomp (C := SSet.{0}) _ (columnIso f.left k).hom

/-- The full original comma fiber bar reconstructs the original row bar weakly. -/
theorem totalBarMap_diagonal_weak (f : Arrow BiSSet.{0}) :
    WeakEquivalence (C := SSet.{0}) (diagonalFunctor.map (totalBarMap f)) := by
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
  exact DaggerOriginalDiagonalGeometric.diagMap_geometric_column
    (totalBarMap f)
    (fun k ↦ (DaggerSSetGluing.weakEquivalence_iff_GW _).mp
      (totalBarMap_column_weak f k))

#print axioms totalBarMap_column_triangle
#print axioms totalBarMap_column_weak
#print axioms totalBarMap_diagonal_weak

end

end DaggerModels.PartII.BisimplicialCommaBarReconstruction
