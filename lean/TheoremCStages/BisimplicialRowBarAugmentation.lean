import SimplexElementsFirstVertexWeak
import ColumnElementsVerticalNaturality
import NativeBisimplicialDiagonal
import OriginalDiagonalGeometricReconciledRecovered

/-!
# A natural weak augmentation from the original row bar

Each fixed inner column is the nerve of the Elements category of the
corresponding original simplicial set. The natural first-vertex comparison
therefore assembles before taking the diagonal. Every original row and
both original operator directions are retained.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerNativeBisimplicialHorizontalMapping (BiSSet)
open DaggerNativeBisimplicialDiagonal (diagonalFunctor)
open DaggerNativeSimplicialReplacement (replacement)
open DaggerNativeSimplicialReplacementWeightsChange (changeWeights)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.BisimplicialRowBarAugmentation

open SimplicialReplacementColumnElements (columnIso column_triangle)
open SimplexElementsFirstVertexWeak

noncomputable section

private abbrev flip :=
  flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type 0)

/-- Augment all original fixed-inner columns naturally at once. -/
def flippedAugmentation (X : BiSSet.{0}) : (replacement X).flip ⟶ X.flip :=
  (ColumnElementsVerticalNaturality.columnsIso X).hom ≫
    (Functor.associator X.flip Functor.elementsFunctor nerveFunctor).hom ≫
    Functor.whiskerLeft X.flip firstVertexNatural ≫
    (Functor.rightUnitor X.flip).hom

/-- The complete original row bar augments to the original bisimplicial set. -/
def augmentation (X : BiSSet.{0}) : replacement X ⟶ X :=
  flip.map (flippedAugmentation X)

/-- Every actual fixed-inner column augmentation is weak. -/
theorem column_weak (X : BiSSet.{0}) (k : SimplexCategoryᵒᵖ) :
    WeakEquivalence (C := SSet.{0}) ((flippedAugmentation X).app k) := by
  have : WeakEquivalence (firstVertexElements (X.flip.obj k)) :=
    firstVertexElements_weak (X.flip.obj k)
  change WeakEquivalence (C := SSet.{0})
    ((columnIso X k).hom ≫ firstVertexElements (X.flip.obj k))
  infer_instance

/-- The diagonal augmentation is weak for every original bisimplicial set. -/
theorem diagonal_weak (X : BiSSet.{0}) :
    WeakEquivalence (diagonalFunctor.map (augmentation X)) := by
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
  exact DaggerOriginalDiagonalGeometric.diagMap_geometric_column
    (augmentation X)
    (fun k ↦ (DaggerSSetGluing.weakEquivalence_iff_GW _).mp (column_weak X k))

/-- Changing the original whole row diagram commutes with the full column augmentation. -/
theorem flippedAugmentation_natural {X Y : BiSSet.{0}} (f : X ⟶ Y) :
    flip.map (changeWeights f) ≫ flippedAugmentation Y =
      flippedAugmentation X ≫ flip.map f := by
  apply NatTrans.ext
  funext k
  let fₖ := (flip.map f).app k
  have hcol := column_triangle (𝟭 SimplexCategoryᵒᵖ) X Y f k
  change (columnIso X k).hom ≫ nerveMap (NatTrans.mapElements fₖ) =
    (flip.map (changeWeights f)).app k ≫ (columnIso Y k).hom at hcol
  have hv : nerveMap (NatTrans.mapElements fₖ) ≫
      firstVertexElements (Y.flip.obj k) =
    firstVertexElements (X.flip.obj k) ≫ fₖ :=
      firstVertexElements_natural fₖ
  change (flip.map (changeWeights f)).app k ≫
      ((columnIso Y k).hom ≫ firstVertexElements (Y.flip.obj k)) =
    ((columnIso X k).hom ≫ firstVertexElements (X.flip.obj k)) ≫ fₖ
  calc
    _ = ((flip.map (changeWeights f)).app k ≫ (columnIso Y k).hom) ≫
        firstVertexElements (Y.flip.obj k) := (Category.assoc _ _ _).symm
    _ = ((columnIso X k).hom ≫ nerveMap (NatTrans.mapElements fₖ)) ≫
        firstVertexElements (Y.flip.obj k) :=
      congrArg (fun m ↦ m ≫ firstVertexElements (Y.flip.obj k)) hcol.symm
    _ = (columnIso X k).hom ≫
        (nerveMap (NatTrans.mapElements fₖ) ≫ firstVertexElements (Y.flip.obj k)) :=
      Category.assoc _ _ _
    _ = (columnIso X k).hom ≫
        (firstVertexElements (X.flip.obj k) ≫ fₖ) :=
      congrArg (fun m ↦ (columnIso X k).hom ≫ m) hv
    _ = _ := (Category.assoc _ _ _).symm

/-- The augmentation is natural as an equality of the original bisimplicial maps. -/
theorem augmentation_natural {X Y : BiSSet.{0}} (f : X ⟶ Y) :
    changeWeights f ≫ augmentation Y = augmentation X ≫ f := by
  apply NatTrans.ext
  funext q
  apply NatTrans.ext
  funext k x
  exact congrFun (NatTrans.congr_app
    (NatTrans.congr_app (flippedAugmentation_natural f) k) q) x

#print axioms flippedAugmentation
#print axioms diagonal_weak
#print axioms augmentation_natural

end

end DaggerModels.PartII.BisimplicialRowBarAugmentation
