import HorizontalMappingVerticalDiagonal
import OrdinarySegalCotensorSegal
import OrdinarySegalVerticalPrecompletion
import NativeBisimplicialDiagonalWeak

/-!
# Strict Segal tests of the corrected vertical precompletion

Every fixed horizontal discrete test commutes with the vertical diagonal.
This proves the literal Segal condition of the precompletion, without
claiming fibrancy or Segal recognition after a fibrant replacement.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerNativeBisimplicialHorizontalMapping (horizontalPre)
open DaggerNativeBisimplicialDiagonal (diagonalFunctor)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalVerticalDiagonalTests

open OrdinaryCSSLocalization (Space discrete)
open HorizontalMappingVerticalDiagonal

noncomputable section

/-- Both actual mapping-space isomorphisms retain the original discrete test map. -/
theorem discreteTest_triangle {K L : SSet.{0}} (i : K ⟶ L)
    (R : SimplexCategoryᵒᵖ ⥤ Space) :
    diagramMappingPrecomp (discrete.map i) (verticalDiagonal R) ≫
        (diagramMappingDiagonalIso K R).hom =
      (diagramMappingDiagonalIso L R).hom ≫
        diagonalFunctor.map (Functor.whiskerLeft R (horizontalPreNatural i)) := by
  have hd := OrdinaryDiscreteMapping.mappingIso_natural i (verticalDiagonal R)
  have hh := horizontalPre_triangle i R
  calc
    _ = (diagramMappingPrecomp (discrete.map i) (verticalDiagonal R) ≫
          (OrdinaryDiscreteMapping.mappingIso K (verticalDiagonal R)).hom) ≫
            (horizontalMappingDiagonalIso K R).hom := by
      simp only [diagramMappingDiagonalIso, Iso.trans_hom, Category.assoc]
    _ = ((OrdinaryDiscreteMapping.mappingIso L (verticalDiagonal R)).hom ≫
          horizontalPre i (verticalDiagonal R)) ≫
            (horizontalMappingDiagonalIso K R).hom :=
      congrArg (fun m ↦ m ≫ (horizontalMappingDiagonalIso K R).hom) hd
    _ = (OrdinaryDiscreteMapping.mappingIso L (verticalDiagonal R)).hom ≫
          ((horizontalMappingDiagonalIso L R).hom ≫
            diagonalFunctor.map (Functor.whiskerLeft R (horizontalPreNatural i))) := by
      simpa only [Category.assoc] using congrArg
        (fun m ↦ (OrdinaryDiscreteMapping.mappingIso L (verticalDiagonal R)).hom ≫ m) hh
    _ = _ := by simp only [diagramMappingDiagonalIso, Iso.trans_hom, Category.assoc]

/-- Rowwise weakness of the same horizontal discrete test passes to the
literal vertical diagonal, without a fibrancy hypothesis. -/
theorem discreteTest_weak {K L : SSet.{0}} (i : K ⟶ L)
    (R : SimplexCategoryᵒᵖ ⥤ Space)
    (hR : ∀ q, WeakEquivalence (diagramMappingPrecomp (discrete.map i) (R.obj q))) :
    WeakEquivalence (diagramMappingPrecomp (discrete.map i) (verticalDiagonal R)) := by
  have hrow (q : SimplexCategoryᵒᵖ) :
      WeakEquivalence (horizontalPre i (R.obj q)) := by
    have : WeakEquivalence (diagramMappingPrecomp (discrete.map i) (R.obj q)) := hR q
    exact weakEquivalence_of_precomp_of_fac
      (OrdinaryDiscreteMapping.mappingIso_natural i (R.obj q)).symm
  have : WeakEquivalence
      (diagonalFunctor.map (Functor.whiskerLeft R (horizontalPreNatural i))) :=
    DaggerNativeBisimplicialDiagonalWeak.diagonal_map_weak
      (Functor.whiskerLeft R (horizontalPreNatural i)) hrow
  exact weakEquivalence_of_postcomp_of_fac (discreteTest_triangle i R)

/-- All literal Segal tests pass to the vertical diagonal of the original row diagram. -/
theorem verticalDiagonal_segalCondition (R : SimplexCategoryᵒᵖ ⥤ Space)
    (hR : ∀ q, OrdinaryCSSConditions.segalCondition (R.obj q)) :
    OrdinaryCSSConditions.segalCondition (verticalDiagonal R) := by
  intro n hn
  apply (weakEquivalence_iff _).mp
  exact discreteTest_weak (DaggerNativeStandardSpineInner.spine n).ι R
    (fun q ↦ (weakEquivalence_iff _).mpr (hR q n hn))

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- The corrected precompletion satisfies every original strict Segal test.
Fibrancy and the Segal property of a replacement remain separate obligations. -/
theorem precompletion_segalCondition (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) :
    OrdinaryCSSConditions.segalCondition
      (OrdinarySegalVerticalPrecompletion.precompletion W) :=
  verticalDiagonal_segalCondition (OrdinarySegalPrecompletion.resolution W)
    (fun q ↦ OrdinarySegalCotensorSegal.cotensor_segalCondition
      (GroupoidSimplex.parameter.obj q.unop) W hSegal)

#print axioms discreteTest_triangle
#print axioms discreteTest_weak
#print axioms verticalDiagonal_segalCondition
#print axioms precompletion_segalCondition

end

end DaggerModels.PartII.OrdinarySegalVerticalDiagonalTests
