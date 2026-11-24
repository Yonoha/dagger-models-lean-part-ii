import NativeSimplicialReplacementWeightsChange
import NativeBisimplicialDiagonalWeak
import TopCatModelCategory.ModelCategorySSet

/-!
# Pointwise Kan replacement of a diagram and its full simplicial replacement

The original diagram need not have Kan values. The unit is retained on each
whole value and on every whole simplicial-replacement cell.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory HomotopicalAlgebra Simplicial Opposite
open DaggerNativeSimplicialReplacementCells (first)
open DaggerNativeSimplicialReplacementWeightsChange (changeWeights diagonalChange)
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.SimplicialReplacementPointwiseKan

noncomputable section

variable {C : Type u} [Category.{u} C]

/-- Pointwise weak maps remain weak on each entire replacement row. -/
theorem changeWeights_row_weak {G H : C ⥤ SSet.{u}} (η : G ⟶ H)
    (hη : ∀ c, WeakEquivalence (η.app c)) (q : SimplexCategoryᵒᵖ) :
    WeakEquivalence ((changeWeights η).app q) :=
  DaggerNativeFamilyWeak.familyMap_weak
    (fun c ↦ η.app (first c)) (fun c ↦ hη (first c))

/-- The literal diagonal map retains pointwise weak equivalences. -/
theorem diagonalChange_weak {G H : C ⥤ SSet.{u}} (η : G ⟶ H)
    (hη : ∀ c, WeakEquivalence (η.app c)) :
    WeakEquivalence (diagonalChange η) :=
  DaggerNativeBisimplicialDiagonalWeak.diagonal_map_weak
    (changeWeights η) (changeWeights_row_weak η hη)

/-- Singular realization provides functorial Kan values. -/
def kanDiagram (G : C ⥤ SSet.{u}) : C ⥤ SSet.{u} :=
  G ⋙ SSet.toTop ⋙ TopCat.toSSet

instance kanDiagram_value_fibrant (G : C ⥤ SSet.{u}) (c : C) :
    IsFibrant ((kanDiagram G).obj c) := by
  change IsFibrant (TopCat.toSSet.obj (SSet.toTop.obj (G.obj c)))
  infer_instance

/-- The original realization unit at every value, with its full naturality. -/
def kanUnit (G : C ⥤ SSet.{u}) : G ⟶ kanDiagram G :=
  Functor.whiskerLeft G sSetTopAdj.unit

theorem kanUnit_value_weak (G : C ⥤ SSet.{u}) (c : C) :
    WeakEquivalence ((kanUnit G).app c) := by
  change WeakEquivalence (sSetTopAdj.unit.app (G.obj c))
  infer_instance

/-- Weak transports remain weak after the pointwise Kan replacement. -/
theorem kanDiagram_map_weak (G : C ⥤ SSet.{u})
    (hG : ∀ ⦃a b : C⦄ (f : a ⟶ b), WeakEquivalence (G.map f))
    {a b : C} (f : a ⟶ b) : WeakEquivalence ((kanDiagram G).map f) := by
  have : WeakEquivalence (G.map f) := hG f
  change WeakEquivalence (TopCat.toSSet.map (SSet.toTop.map (G.map f)))
  infer_instance

/-- The actual full replacement diagonal maps weakly to its Kan-value version. -/
theorem kanUnit_diagonal_weak (G : C ⥤ SSet.{u}) :
    WeakEquivalence (diagonalChange (kanUnit G)) :=
  diagonalChange_weak (kanUnit G) (kanUnit_value_weak G)

#print axioms changeWeights_row_weak
#print axioms diagonalChange_weak
#print axioms kanDiagram_map_weak
#print axioms kanUnit_diagonal_weak

end

end DaggerModels.PartII.SimplicialReplacementPointwiseKan
