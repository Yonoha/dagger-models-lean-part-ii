import SimplicialReplacementChosenHomotopyFiber
import DaggerModelsPartII.ChosenHomotopyFiberTriangle

/-!
# The original replacement value as a chosen homotopy fiber

The exact original strict fiber is mapped to the chosen fiber of its
unchanged diagonal projection. A comparison through the actual relative
Reedy fibration proves that this canonical inclusion is weak whenever
the original diagram has Kan values and weak transition maps.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Simplicial Opposite HomotopicalAlgebra
open DaggerNativeBisimplicialHorizontalMapping (BiSSet)
open DaggerNativeBisimplicialDiagonal (diagonalFunctor)
open DaggerNativeSimplicialReplacement (projection)
open DaggerNativeReedyRelativeReplacement
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.SimplicialReplacementValueChosenFiber

universe u

noncomputable section

variable {C : Type u} [Category.{u} C]

private abbrev arrow (G : C ⥤ SSet.{u}) : Arrow BiSSet.{u} :=
  Arrow.mk (projection G)
private abbrev oldMap (G : C ⥤ SSet.{u}) := diagonalFunctor.map (projection G)
private abbrev newMap (G : C ⥤ SSet.{u}) :=
  diagonalFunctor.map (relativeReplacement.obj (arrow G)).hom
private abbrev totalMap (G : C ⥤ SSet.{u}) :=
  diagonalFunctor.map (totalUnit (arrow G))
private abbrev baseMap (G : C ⥤ SSet.{u}) :=
  diagonalFunctor.map (baseUnit (arrow G))
private abbrev pointMap (c : C) :=
  diagonalFunctor.map
    (SimplicialReplacementChosenHomotopyFiber.coherentPoint c)
private abbrev newPoint {G : C ⥤ SSet.{u}} (c : C) :=
  diagonalFunctor.map
    (SimplicialReplacementChosenHomotopyFiber.coherentPoint c ≫ baseUnit (arrow G))

/-- The unchanged original value enters the chosen homotopy fiber through
its exact strict-fiber isomorphism. -/
def valueToChosen (G : C ⥤ SSet.{u}) (c : C) :
    G.obj c ⟶
      ChosenHomotopyFiberComparison.chosenFiber (oldMap G) (pointMap c) :=
  (SimplicialReplacementChosenHomotopyFiber.originalFiberIso G c).hom ≫
    ChosenHomotopyFiberTriangle.inclusion (oldMap G) (pointMap c)

private theorem square (G : C ⥤ SSet.{u}) :
    oldMap G ≫ baseMap G = totalMap G ≫ newMap G := by
  rw [← diagonalFunctor.map_comp, ← diagonalFunctor.map_comp,
    unit_square]
  rfl

private theorem point_square (G : C ⥤ SSet.{u}) (c : C) :
    pointMap c ≫ baseMap G = newPoint (G := G) c := by
  exact (diagonalFunctor.map_comp _ _).symm

private theorem imageComparison_eq (G : C ⥤ SSet.{u}) (c : C) :
    DaggerNativeRelativeReedyBisimplicialFibres.imageComparison
        diagonalFunctor (arrow G)
          (SimplicialReplacementChosenHomotopyFiber.coherentPoint c) =
      DaggerNativeSSetFibrationSquareFibreWeak.fibreMap
        (oldMap G) (newMap G) (totalMap G) (baseMap G)
        (square G) (pointMap c) (newPoint (G := G) c) (point_square G c) := by
  rfl

variable (G : C ⥤ SSet.{u}) [∀ a, IsFibrant (G.obj a)]
variable (hG : ∀ ⦃a b : C⦄ (g : a ⟶ b), WeakEquivalence (G.map g))

include hG in
/-- The exact value-to-chosen-fiber map is weak, with the original
bisimplicial point object and both original unit maps retained. -/
theorem valueToChosen_weak (c : C) : WeakEquivalence (valueToChosen G c) := by
  haveI : Fibration (newMap G) :=
    SimplicialReplacementChosenHomotopyFiber.relative_diagonal_fibration G hG
  haveI : WeakEquivalence (totalMap G) :=
    SimplicialReplacementChosenHomotopyFiber.total_diagonal_unit_weak G
  haveI : WeakEquivalence (baseMap G) :=
    SimplicialReplacementChosenHomotopyFiber.base_diagonal_unit_weak G
  let comparison := ChosenHomotopyFiberComparison.comparison
    (oldMap G) (newMap G) (totalMap G) (baseMap G)
    (square G) (pointMap c) (newPoint (G := G) c) (point_square G c)
  haveI : WeakEquivalence comparison :=
    ChosenHomotopyFiberComparison.comparison_weak
      (oldMap G) (newMap G) (totalMap G) (baseMap G)
      (square G) (pointMap c) (newPoint (G := G) c) (point_square G c)
  haveI : WeakEquivalence
      (SimplicialReplacementChosenHomotopyFiber.chosenFiberComparison G c) :=
    SimplicialReplacementChosenHomotopyFiber.chosenFiberComparison_weak G c
  have htriangle : valueToChosen G c ≫ comparison =
      SimplicialReplacementChosenHomotopyFiber.chosenFiberComparison G c := by
    unfold valueToChosen SimplicialReplacementChosenHomotopyFiber.chosenFiberComparison
    rw [Category.assoc,
      ChosenHomotopyFiberTriangle.inclusion_comparison
        (oldMap G) (newMap G) (totalMap G) (baseMap G)
        (square G) (pointMap c) (newPoint (G := G) c) (point_square G c),
      ← imageComparison_eq]
    rfl
  exact weakEquivalence_of_postcomp_of_fac htriangle

#print axioms valueToChosen
#print axioms valueToChosen_weak

end

end DaggerModels.PartII.SimplicialReplacementValueChosenFiber
