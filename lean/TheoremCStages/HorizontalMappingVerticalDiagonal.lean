import OrdinaryDiscreteMapping
import NativeBisimplicialDiagonal

/-!
# Horizontal mapping through the corrected vertical diagonal

The horizontal mapping object of the vertical diagonal is the diagonal
of the original rowwise horizontal mapping objects. The original outer,
horizontal, and inner simplex operators all remain in their given order.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial
open DaggerNativeBisimplicialHorizontalMapping
open DaggerNativeBisimplicialDiagonal (diagonalFunctor)
open DaggerModels.PartII.OrdinaryCSSLocalization (Space)

namespace DaggerModels.PartII.HorizontalMappingVerticalDiagonal
noncomputable section

/-- Take the native diagonal in the two vertical directions, retaining
the original horizontal simplicial degree. -/
def verticalDiagonal (R : SimplexCategoryᵒᵖ ⥤ Space) : Space :=
  R.flip ⋙ diagonalFunctor

/-- Horizontal mapping is a functor of the complete horizontal space. -/
def horizontalMappingFunctor (K : SSet.{0}) : Space ⥤ SSet.{0} where
  obj X := horizontalMapping K X
  map f := horizontalMap K f
  map_id X := horizontalMap_id K X
  map_comp f g := horizontalMap_comp K f g

/-- Precomposition by the actual simplicial map is natural in the
original complete horizontal space. -/
def horizontalPreNatural {K L : SSet.{0}} (i : K ⟶ L) :
    horizontalMappingFunctor L ⟶ horizontalMappingFunctor K where
  app X := horizontalPre i X
  naturality {_ _} f := horizontalPre_natural i f

/-- The two constructions have the same horizontal target functor at
each vertical degree, including all horizontal operators. -/
private theorem horizontalSlice_eq (R : SimplexCategoryᵒᵖ ⥤ Space)
    (q : SimplexCategoryᵒᵖ) :
    (verticalDiagonal R).flip.obj q = (R.obj q).flip.obj q := by
  apply CategoryTheory.Functor.hext
  · intro n
    rfl
  · intro n m θ
    rfl

/-- Horizontal mapping commutes with the vertical diagonal by an
identity-component isomorphism, not by a fibrant replacement. -/
def horizontalMappingDiagonalIso (K : SSet.{0})
    (R : SimplexCategoryᵒᵖ ⥤ Space) :
    horizontalMapping K (verticalDiagonal R) ≅
      diagonalFunctor.obj (R ⋙ horizontalMappingFunctor K) :=
  NatIso.ofComponents (fun q ↦ by
    change (K ⟶ (verticalDiagonal R).flip.obj q) ≅
      (K ⟶ (R.obj q).flip.obj q)
    rw [horizontalSlice_eq R q]) (by
      intro q r α
      funext a
      apply NatTrans.ext
      funext n x
      rfl)

/-- The comparison preserves precomposition by each literal map
`i : K ⟶ L` on both sides of the diagonal. -/
theorem horizontalPre_triangle {K L : SSet.{0}} (i : K ⟶ L)
    (R : SimplexCategoryᵒᵖ ⥤ Space) :
    horizontalPre i (verticalDiagonal R) ≫
        (horizontalMappingDiagonalIso K R).hom =
      (horizontalMappingDiagonalIso L R).hom ≫
        diagonalFunctor.map (Functor.whiskerLeft R (horizontalPreNatural i)) := by
  apply NatTrans.ext
  funext q a
  apply NatTrans.ext
  funext n x
  rfl

/-- The checked discrete mapping-space isomorphism gives the same
strict vertical diagonal without altering the input diagram. -/
def diagramMappingDiagonalIso (K : SSet.{0})
    (R : SimplexCategoryᵒᵖ ⥤ Space) :
    diagramMappingSpace (OrdinaryCSSLocalization.discrete.obj K) (verticalDiagonal R) ≅
      diagonalFunctor.obj (R ⋙ horizontalMappingFunctor K) :=
  OrdinaryDiscreteMapping.mappingIso K (verticalDiagonal R) ≪≫
    horizontalMappingDiagonalIso K R

#print axioms horizontalMappingFunctor
#print axioms horizontalPreNatural
#print axioms horizontalMappingDiagonalIso
#print axioms horizontalPre_triangle
#print axioms diagramMappingDiagonalIso

end
end DaggerModels.PartII.HorizontalMappingVerticalDiagonal
