import OrdinaryAllVertexSquareComparison
import OrdinarySegalConstantGroupoidSimplexFullyFaithful
import OrdinarySegalPrecompletion
import NativeSSetFibrationsOverBaseWeakPullbacks

/-!
# The actual constant section on every finite ordered vertex tuple

The original constant section into the groupoid-simplex cotensor induces a
weak all-vertex square in every horizontal degree. Base change of that
square compares the strict fiber over any original complete vertex tuple
with the corresponding strict fiber of the target pullback. This is a
rowwise statement before the diagonal corrected unit or completion.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalAllVertexUnitFibres

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalVertexTupleFibres (vertices vertexMap)
open OrdinarySegalHorizontalCotensor (cotensor)
open OrdinarySegalHorizontalCotensorPoint (constantSection)
open OrdinaryAllVertexSquareComparison (vertexComparison)
open DaggerNativeSSetFibrationsOverBaseWeakPullbacks (mapOver)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev E (q : SimplexCategory) : SSet.{0} :=
  GroupoidSimplex.parameter.obj q

/-- The constant section gives a weak square on all original ordered vertices. -/
theorem constantSection_vertexComparison_weak (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (q : SimplexCategory) (n : ℕ) :
    WeakEquivalence (vertexComparison (constantSection (E q) W) n) := by
  have : IsFibrant (cotensor (E q) W) :=
    OrdinarySegalCotensorFibrant.cotensor_injectiveFibrant (E q) W inferInstance
  apply OrdinaryAllVertexSquareComparison.vertexComparison_weak
    (constantSection (E q) W) hSegal
    (OrdinarySegalCotensorSegal.cotensor_segalCondition (E q) W hSegal)
  intro x y
  exact OrdinarySegalConstantGroupoidSimplexFullyFaithful.mappingMap_weak
    W hSegal q ⟨0, Nat.zero_lt_succ _⟩ x y

/-- The complete target tuple map of the original constant section. -/
def vertexBaseMap (W : Space) (q : SimplexCategory) (n : ℕ) :
    diagramMappingSpace (discrete.obj (vertices n)) W ⟶
      diagramMappingSpace (discrete.obj (vertices n)) (cotensor (E q) W) :=
  diagramMappingPostcomp (discrete.obj (vertices n)) (constantSection (E q) W)

/-- The strict base change of the original full-tuple square at any tuple point. -/
def strictTupleComparison (W : Space) (q : SimplexCategory) (n : ℕ)
    (b : (Δ[0] : SSet.{0}) ⟶ diagramMappingSpace (discrete.obj (vertices n)) W) :
    pullback (vertexMap W n) b ⟶
      pullback
        (pullback.snd (vertexMap (cotensor (E q) W) n) (vertexBaseMap W q n)) b :=
  mapOver (vertexMap W n)
    (pullback.snd (vertexMap (cotensor (E q) W) n) (vertexBaseMap W q n))
    (vertexComparison (constantSection (E q) W) n)
    (by
      unfold vertexBaseMap
      simp only [vertexComparison, pullback.lift_snd]) b

/-- Every actual complete-tuple strict fiber base change is weak. -/
theorem strictTupleComparison_weak (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (q : SimplexCategory) (n : ℕ)
    (b : (Δ[0] : SSet.{0}) ⟶ diagramMappingSpace (discrete.obj (vertices n)) W) :
    WeakEquivalence (strictTupleComparison W q n b) := by
  have : IsFibrant (cotensor (E q) W) :=
    OrdinarySegalCotensorFibrant.cotensor_injectiveFibrant (E q) W inferInstance
  have : Fibration (vertexMap W n) :=
    OrdinarySegalVertexTupleFibres.vertexMap_fibration W n
  have : Fibration (vertexMap (cotensor (E q) W) n) :=
    OrdinarySegalVertexTupleFibres.vertexMap_fibration (cotensor (E q) W) n
  have : Fibration
      (pullback.snd (vertexMap (cotensor (E q) W) n) (vertexBaseMap W q n)) :=
    inferInstance
  have : WeakEquivalence (vertexComparison (constantSection (E q) W) n) :=
    constantSection_vertexComparison_weak W hSegal q n
  unfold strictTupleComparison
  exact DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver_weakEquivalence
    (vertexMap W n)
    (pullback.snd (vertexMap (cotensor (E q) W) n) (vertexBaseMap W q n))
    (vertexComparison (constantSection (E q) W) n)
    (by
      unfold vertexBaseMap
      simp only [vertexComparison, pullback.lift_snd]) b

#print axioms constantSection_vertexComparison_weak
#print axioms strictTupleComparison_weak

end

end DaggerModels.PartII.OrdinarySegalAllVertexUnitFibres
