import OrdinarySegalConstantIntervalFullyFaithful
import OrdinarySegalCotensorOrderedMappingFibration
import OrdinarySegalCotensorUnitMappingDiagonal
import OrdinarySegalOrderedMappingComposition
import KanHomotopyMonomorphismCancellation

/-!
# The actual constant walking-isomorphism section is fully faithful

Restricting along the original walking unit gives the checked constant
interval section. On the exact ordered mapping fibers this composite is
weak. The restriction is a Kan fibration with weak strict diagonal, so
the checked Kan cancellation proves the original constant walking section
weak on those same fibers. Ordinary completeness is not assumed.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalConstantWalkingFullyFaithful

open OrdinaryCSSLocalization (Space)
open OrdinarySegalHorizontalCotensor (cotensor pre)
open OrdinarySegalHorizontalCotensorPoint (constantSection)
open OrdinarySegalOrderedMappingFibres
open OrdinarySegalOrderedMappingMaps
open OrdinarySegalOrderedMappingComposition

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev J := GroupoidSimplex.parameter.obj ⦋1⦌
private abbrev unit := JTCylinderCEComparison.simplexUnit.app ⦋1⦌

/-- The original constant walking-isomorphism section induces a Kan weak
equivalence on every literal ordered mapping fiber. -/
theorem mappingMap_weak (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    WeakEquivalence (mappingMap (constantSection J W) x y) := by
  have : IsFibrant (cotensor J W) :=
    OrdinarySegalCotensorFibrant.cotensor_injectiveFibrant J W inferInstance
  have : IsFibrant (cotensor (Δ[1] : SSet.{0}) W) :=
    OrdinarySegalCotensorFibrant.cotensor_injectiveFibrant _ W inferInstance
  have : Mono unit := JTSimplexUnitKan.simplexUnit_mono ⦋1⦌
  let a := constantSection J W
  let b := pre unit W
  let ax := (a.app (op ⦋0⦌)).app (op ⦋0⦌) x
  let ay := (a.app (op ⦋0⦌)).app (op ⦋0⦌) y
  let i := mappingMap a x y
  let j := mappingMap b ax ay
  have : IsFibrant (mappingFiber W x y) := mappingFiber_isFibrant W x y
  have : IsFibrant (mappingFiber (cotensor J W) ax ay) :=
    mappingFiber_isFibrant _ ax ay
  have : IsFibrant (mappingFiber (cotensor (Δ[1] : SSet.{0}) W)
      ((b.app (op ⦋0⦌)).app (op ⦋0⦌) ax)
      ((b.app (op ⦋0⦌)).app (op ⦋0⦌) ay)) := mappingFiber_isFibrant _ _ _
  have : Fibration j :=
    OrdinarySegalCotensorOrderedMappingFibration.mappingMap_fibration unit W ax ay
  have : WeakEquivalence (KanHomotopyMonomorphism.diagonal j) :=
    OrdinarySegalCotensorUnitMappingDiagonal.unit_mappingMap_diagonal_weak W hSegal ax ay
  have : WeakEquivalence (i ≫ j) := by
    dsimp only [i, j, ax, ay]
    rw [mappingMap_comp]
    have h : a ≫ b = constantSection (Δ[1] : SSet.{0}) W :=
      constantSection_pre unit W
    have ht : ∀ (c : W ⟶ cotensor (Δ[1] : SSet.{0}) W),
        c = constantSection (Δ[1] : SSet.{0}) W →
          WeakEquivalence (mappingMap c x y) := by
      intro c hc
      subst c
      exact OrdinarySegalConstantIntervalFullyFaithful.mappingMap_weak W hSegal x y
    exact ht (a ≫ b) h
  exact (KanHomotopyMonomorphismCancellation.weak_pair_of_composite_and_diagonal i j).2

#print axioms mappingMap_weak

end
end DaggerModels.PartII.OrdinarySegalConstantWalkingFullyFaithful
