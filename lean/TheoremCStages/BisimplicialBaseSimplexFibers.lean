import EquifiberedFiberBaseChange
import Mathlib.CategoryTheory.Comma.Basic

/-!
# Fibers over simplices of an equifibered bisimplicial arrow

An object of the comma category specifies an outer degree and an actual
standard simplex in that degree's base. A morphism changes both indices
subject to its original commutative square. Strict pullback fibers form a
functor on this comma category; when the rows are fibrations and the outer
arrow is equifibered, every map of that functor is weak.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerNativeBisimplicialHorizontalMapping (BiSSet)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.BisimplicialBaseSimplexFibers

noncomputable section

/-- Simplices in every actual outer row of the base, with both simplex
and outer degree allowed to vary. -/
abbrev Index (f : Arrow BiSSet.{0}) := Comma SSet.stdSimplex f.right

/-- The strict pullback of one row projection at the specified simplex. -/
def fiber (f : Arrow BiSSet.{0}) (σ : Index f) : SSet.{0} :=
  pullback (f.hom.app σ.right) σ.hom

/-- The actual square induced by a comma morphism on the two specified
strict pullbacks. -/
def fiberMap (f : Arrow BiSSet.{0}) {σ τ : Index f} (a : σ ⟶ τ) :
    fiber f σ ⟶ fiber f τ :=
  SSetWeakPullbackComparison.comparison
    (f.hom.app σ.right) (f.hom.app τ.right)
    (f.left.map a.right) (f.right.map a.right)
    (f.hom.naturality a.right).symm
    σ.hom τ.hom (SSet.stdSimplex.map a.left) a.w.symm

theorem fiberMap_fst (f : Arrow BiSSet.{0}) {σ τ : Index f}
    (a : σ ⟶ τ) :
    fiberMap f a ≫ pullback.fst (f.hom.app τ.right) τ.hom =
      pullback.fst (f.hom.app σ.right) σ.hom ≫
        f.left.map a.right :=
  SSetWeakPullbackComparison.comparison_fst _ _ _ _ _ _ _ _ _

theorem fiberMap_snd (f : Arrow BiSSet.{0}) {σ τ : Index f}
    (a : σ ⟶ τ) :
    fiberMap f a ≫ pullback.snd (f.hom.app τ.right) τ.hom =
      pullback.snd (f.hom.app σ.right) σ.hom ≫
        SSet.stdSimplex.map a.left :=
  SSetWeakPullbackComparison.comparison_snd _ _ _ _ _ _ _ _ _

/-- The pointwise pullbacks and their actual comparison maps form a
functor on the full comma category. -/
def fiberDiagram (f : Arrow BiSSet.{0}) : Index f ⥤ SSet.{0} where
  obj σ := fiber f σ
  map a := fiberMap f a
  map_id σ := by
    apply pullback.hom_ext
    · rw [fiberMap_fst, Category.id_comp]
      change pullback.fst (f.hom.app σ.right) σ.hom ≫
        f.left.map (𝟙 σ.right) = _
      exact (congrArg
        (fun t ↦ pullback.fst (f.hom.app σ.right) σ.hom ≫ t)
        (f.left.map_id σ.right)).trans (Category.comp_id _)
    · rw [fiberMap_snd, Category.id_comp]
      change pullback.snd (f.hom.app σ.right) σ.hom ≫
        SSet.stdSimplex.map (𝟙 σ.left) = _
      exact (congrArg
        (fun t ↦ pullback.snd (f.hom.app σ.right) σ.hom ≫ t)
        (SSet.stdSimplex.map_id σ.left)).trans (Category.comp_id _)
  map_comp a b := by
    apply pullback.hom_ext
    · rw [fiberMap_fst, Category.assoc, fiberMap_fst,
        ← Category.assoc, fiberMap_fst]
      change _ ≫ f.left.map (a.right ≫ b.right) = _
      rw [f.left.map_comp, Category.assoc]
    · rw [fiberMap_snd, Category.assoc, fiberMap_snd,
        ← Category.assoc, fiberMap_snd]
      change _ ≫ SSet.stdSimplex.map (a.left ≫ b.left) = _
      rw [SSet.stdSimplex.map_comp, Category.assoc]

/-- The full fiber diagram retains its original total-row coordinate. -/
def totalProjection (f : Arrow BiSSet.{0}) :
    fiberDiagram f ⟶
      Comma.snd SSet.stdSimplex f.right ⋙ f.left where
  app σ := pullback.fst (f.hom.app σ.right) σ.hom
  naturality := by
    intro σ τ a
    exact fiberMap_fst f a

/-- The full fiber diagram also retains the specified standard-simplex
coordinate of every comma object. -/
def simplexProjection (f : Arrow BiSSet.{0}) :
    fiberDiagram f ⟶
      Comma.fst SSet.stdSimplex f.right ⋙ SSet.stdSimplex where
  app σ := pullback.snd (f.hom.app σ.right) σ.hom
  naturality := by
    intro σ τ a
    exact fiberMap_snd f a

/-- Every comma morphism acts weakly on its actual strict fiber when
the row maps are fibrations and the outer arrow is equifibered. -/
theorem fiberMap_weak (f : Arrow BiSSet.{0})
    (hFib : ∀ q, Fibration (f.hom.app q))
    (hEqui : BisimplicialEquifibered.Equifibered f)
    {σ τ : Index f} (a : σ ⟶ τ) :
    WeakEquivalence (fiberMap f a) := by
  haveI : Fibration (f.hom.app σ.right) := hFib σ.right
  haveI : Fibration (f.hom.app τ.right) := hFib τ.right
  haveI : WeakEquivalence (SSet.stdSimplex.map a.left) :=
    EquifiberedFiberBaseChange.standardSimplexMap_weak a.left
  have hc : WeakEquivalence
      (pullback.lift (f.left.map a.right) (f.hom.app σ.right)
        (f.hom.naturality a.right)) := hEqui a.right
  exact EquifiberedFiberBaseChange.comparison_weak_of_transition
    (f.hom.app σ.right) (f.hom.app τ.right)
    (f.left.map a.right) (f.right.map a.right)
    (f.hom.naturality a.right).symm
    σ.hom τ.hom (SSet.stdSimplex.map a.left) a.w.symm hc

/-- Every arrow in the full comma index is sent to a weak equivalence. -/
theorem fiberDiagram_map_weak (f : Arrow BiSSet.{0})
    (hFib : ∀ q, Fibration (f.hom.app q))
    (hEqui : BisimplicialEquifibered.Equifibered f)
    {σ τ : Index f} (a : σ ⟶ τ) :
    WeakEquivalence ((fiberDiagram f).map a) :=
  fiberMap_weak f hFib hEqui a

#print axioms fiberDiagram
#print axioms totalProjection
#print axioms simplexProjection
#print axioms fiberMap_weak

end

end DaggerModels.PartII.BisimplicialBaseSimplexFibers
