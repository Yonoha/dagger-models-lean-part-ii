import OrdinaryGroupoidSimplexCotensorObjectWitness
import OrdinaryGroupoidSimplexCotensorTransitionHomotopy
import OrdinarySegalCoherentSourceTransport
import OrdinarySegalCoherentTargetTransport
import OrdinarySegalConstantGroupoidSimplexFullyFaithful
import OrdinarySegalOrderedMappingComposition
import OrdinarySegalOrderedMappingWeakCongruence

/-!
# Ordered mapping fibers of original groupoid-simplex transitions

The actual restriction along any original simplex operator is weak on every
literal ordered mapping fiber. Coherent source and target witnesses reduce
the two arbitrary cotensor vertices to constant-section vertices. At those
vertices, the strict naturality of the constant section and two-out-of-three
give the result. No completeness hypothesis is used.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryGroupoidSimplexTransitionFullyFaithful

open OrdinaryCSSLocalization (Space)
open OrdinarySegalHorizontalCotensor (cotensor)
open OrdinarySegalHorizontalCotensorPoint (constantSection)
open OrdinarySegalOrderedMappingMaps (mappingMap)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev E (k : SimplexCategory) : SSet.{0} :=
  GroupoidSimplex.parameter.obj k

/-- Every original parameter transition is weak on the ordered mapping fiber
at any two actual source cotensor vertices. -/
theorem mappingMap_weak {n m : SimplexCategory} (θ : n ⟶ m)
    (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (z z' : ((cotensor (E m) W).obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    WeakEquivalence
      (mappingMap (OrdinaryGroupoidSimplexCotensorTransitionHomotopy.transition θ W)
        z z') := by
  let X := cotensor (E m) W
  let Y := cotensor (E n) W
  let t := OrdinaryGroupoidSimplexCotensorTransitionHomotopy.transition θ W
  let sₘ := constantSection (E m) W
  let sₙ := constantSection (E n) W
  let j : Fin (m.len + 1) := ⟨0, Nat.zero_lt_succ _⟩
  have : IsFibrant X :=
    OrdinarySegalCotensorFibrant.cotensor_injectiveFibrant (E m) W inferInstance
  have : IsFibrant Y :=
    OrdinarySegalCotensorFibrant.cotensor_injectiveFibrant (E n) W inferInstance
  have hX : OrdinaryCSSConditions.segalCondition X :=
    OrdinarySegalCotensorSegal.cotensor_segalCondition (E m) W hSegal
  have hY : OrdinaryCSSConditions.segalCondition Y :=
    OrdinarySegalCotensorSegal.cotensor_segalCondition (E n) W hSegal
  obtain ⟨x, H, hz, hsx⟩ :=
    OrdinaryGroupoidSimplexCotensorObjectWitness.coherent_object_witness m j W z
  obtain ⟨y, H', hz', hsy⟩ :=
    OrdinaryGroupoidSimplexCotensorObjectWitness.coherent_object_witness m j W z'
  let sx := ((sₘ.app (op ⦋0⦌)).app (op ⦋0⦌)) x
  let sy := ((sₘ.app (op ⦋0⦌)).app (op ⦋0⦌)) y
  have hSource : WeakEquivalence (mappingMap t z z') ↔
      WeakEquivalence (mappingMap t sx z') := by
    have transfer (a b : (X.obj (op ⦋0⦌)).obj (op ⦋0⦌))
        (ha : a = z) (hb : b = sx)
        (h : WeakEquivalence (mappingMap t a z') ↔
          WeakEquivalence (mappingMap t b z')) :
        WeakEquivalence (mappingMap t z z') ↔
          WeakEquivalence (mappingMap t sx z') := by
      subst a
      subst b
      exact h
    exact transfer _ _ hz hsx
      (OrdinarySegalCoherentSourceTransport.mappingMap_weak_iff_actual
        t hX hY H z')
  have hTarget : WeakEquivalence (mappingMap t sx z') ↔
      WeakEquivalence (mappingMap t sx sy) := by
    have transfer (a b : (X.obj (op ⦋0⦌)).obj (op ⦋0⦌))
        (ha : a = z') (hb : b = sy)
        (h : WeakEquivalence (mappingMap t sx a) ↔
          WeakEquivalence (mappingMap t sx b)) :
        WeakEquivalence (mappingMap t sx z') ↔
          WeakEquivalence (mappingMap t sx sy) := by
      subst a
      subst b
      exact h
    exact transfer _ _ hz' hsy
      (OrdinarySegalCoherentTargetTransport.mappingMap_weak_iff_actual
        t hX hY H' sx)
  have hSection : sₘ ≫ t = sₙ :=
    OrdinarySegalOrderedMappingComposition.constantSection_pre
      (GroupoidSimplex.parameter.map θ) W
  have hComposite : WeakEquivalence (mappingMap (sₘ ≫ t) x y) :=
    (OrdinarySegalOrderedMappingWeakCongruence.weak_congr hSection x y).mpr
      (OrdinarySegalConstantGroupoidSimplexFullyFaithful.mappingMap_weak
        W hSegal n (⟨0, Nat.zero_lt_succ _⟩ : Fin (n.len + 1)) x y)
  have hFactor : WeakEquivalence
      (mappingMap sₘ x y ≫ mappingMap t sx sy) := by
    rw [OrdinarySegalOrderedMappingComposition.mappingMap_comp]
    exact hComposite
  have hConstant : WeakEquivalence (mappingMap t sx sy) := by
    have : WeakEquivalence (mappingMap sₘ x y) :=
      OrdinarySegalConstantGroupoidSimplexFullyFaithful.mappingMap_weak
        W hSegal m j x y
    have : WeakEquivalence (mappingMap sₘ x y ≫ mappingMap t sx sy) := hFactor
    exact weakEquivalence_of_precomp (mappingMap sₘ x y) (mappingMap t sx sy)
  exact hSource.mpr (hTarget.mpr hConstant)

#print axioms mappingMap_weak

end
end DaggerModels.PartII.OrdinaryGroupoidSimplexTransitionFullyFaithful
