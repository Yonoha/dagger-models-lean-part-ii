import OrdinaryPrecompletionWalkingHomotopy
import NativeAllCofibrantLocalizationSaturation

/-!
# Corrected precompletion of maps with walking homotopy inverses

The two inverse maps may differ. Their two actual walking homotopies give
weak composites after corrected precompletion. Localization detects weakness
of the middle map from those two composites in each horizontal row.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerNativeAllCofibrantLocalizationSaturation
  (weakEquivalence_iff_localization_isIso)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryPrecompletionCategoricalEquivalence

open OrdinaryCSSLocalization (Space walkingSpace)
open OrdinaryPrecompletionWalkingHomotopy (vertexSection homotopy_row_weak_iff)
open OrdinarySegalVerticalPrecompletionNaturality (precompletionMap)

noncomputable section

/-- Two weak composites force weakness of their common middle map. This is
proved in the actual Kan localization, without postulating a weak two-out-of-six
rule. -/
theorem weak_of_two_composites {X Y Z T : SSet.{0}}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ T)
    (hab : WeakEquivalence (a ≫ b))
    (hbc : WeakEquivalence (b ≫ c)) : WeakEquivalence b := by
  let Q := (weakEquivalences SSet.{0}).Q
  have habIso : IsIso (Q.map a ≫ Q.map b) := by
    rw [← Q.map_comp]
    exact (weakEquivalence_iff_localization_isIso Q (a ≫ b)).mp hab
  have hbcIso : IsIso (Q.map b ≫ Q.map c) := by
    rw [← Q.map_comp]
    exact (weakEquivalence_iff_localization_isIso Q (b ≫ c)).mp hbc
  letI := habIso
  letI := hbcIso
  haveI : IsSplitMono (Q.map b) := IsSplitMono.mk' {
    retraction := Q.map c ≫ inv (Q.map b ≫ Q.map c)
    id := by rw [← Category.assoc, IsIso.hom_inv_id] }
  haveI : IsSplitEpi (Q.map b) := IsSplitEpi.mk' {
    section_ := inv (Q.map a ≫ Q.map b) ≫ Q.map a
    id := by rw [Category.assoc, IsIso.inv_hom_id] }
  haveI : IsIso (Q.map b) := isIso_of_epi_of_isSplitMono (Q.map b)
  exact (weakEquivalence_iff_localization_isIso Q b).mpr inferInstance

/-- Literal categorical inverse data through the same walking-isomorphism
space. The maps, vertices, and two homotopies are retained individually. -/
structure WalkingInverseData {U V : Space} (f : U ⟶ V) where
  leftInverse : V ⟶ U
  rightInverse : V ⟶ U
  sourceVertex₀ : (⊤_ Space) ⟶ walkingSpace
  sourceVertex₁ : (⊤_ Space) ⟶ walkingSpace
  sourceHomotopy : U ⨯ walkingSpace ⟶ U
  sourceComposite : vertexSection U sourceVertex₀ ≫ sourceHomotopy =
    f ≫ rightInverse
  sourceIdentity : vertexSection U sourceVertex₁ ≫ sourceHomotopy = 𝟙 U
  targetVertex₀ : (⊤_ Space) ⟶ walkingSpace
  targetVertex₁ : (⊤_ Space) ⟶ walkingSpace
  targetHomotopy : V ⨯ walkingSpace ⟶ V
  targetComposite : vertexSection V targetVertex₀ ≫ targetHomotopy =
    leftInverse ≫ f
  targetIdentity : vertexSection V targetVertex₁ ≫ targetHomotopy = 𝟙 V

/-- The actual corrected precompletion map is weak in every horizontal row
for a map with two literal walking homotopy inverses. -/
theorem precompletionMap_row_weak_of_walkingInverse
    {U V : Space} (f : U ⟶ V) (d : WalkingInverseData f)
    (n : SimplexCategory) :
    WeakEquivalence ((precompletionMap f).app (op n)) := by
  have hsourceId : WeakEquivalence
      ((precompletionMap
        (vertexSection U d.sourceVertex₁ ≫ d.sourceHomotopy)).app (op n)) := by
    rw [d.sourceIdentity,
      OrdinarySegalVerticalPrecompletionNaturality.precompletionMap_id]
    infer_instance
  have hsource : WeakEquivalence
      ((precompletionMap (f ≫ d.rightInverse)).app (op n)) := by
    have h := (homotopy_row_weak_iff d.sourceVertex₀ d.sourceVertex₁
      d.sourceHomotopy n).mpr hsourceId
    rw [d.sourceComposite] at h
    exact h
  have htargetId : WeakEquivalence
      ((precompletionMap
        (vertexSection V d.targetVertex₁ ≫ d.targetHomotopy)).app (op n)) := by
    rw [d.targetIdentity,
      OrdinarySegalVerticalPrecompletionNaturality.precompletionMap_id]
    infer_instance
  have htarget : WeakEquivalence
      ((precompletionMap (d.leftInverse ≫ f)).app (op n)) := by
    have h := (homotopy_row_weak_iff d.targetVertex₀ d.targetVertex₁
      d.targetHomotopy n).mpr htargetId
    rw [d.targetComposite] at h
    exact h
  let a := (precompletionMap d.leftInverse).app (op n)
  let b := (precompletionMap f).app (op n)
  let c := (precompletionMap d.rightInverse).app (op n)
  have hab : WeakEquivalence (a ≫ b) := by
    change WeakEquivalence
      ((precompletionMap d.leftInverse ≫ precompletionMap f).app (op n))
    rw [← OrdinarySegalVerticalPrecompletionNaturality.precompletionMap_comp]
    exact htarget
  have hbc : WeakEquivalence (b ≫ c) := by
    change WeakEquivalence
      ((precompletionMap f ≫ precompletionMap d.rightInverse).app (op n))
    rw [← OrdinarySegalVerticalPrecompletionNaturality.precompletionMap_comp]
    exact hsource
  exact weak_of_two_composites a b c hab hbc

#print axioms weak_of_two_composites
#print axioms precompletionMap_row_weak_of_walkingInverse

end

end DaggerModels.PartII.OrdinaryPrecompletionCategoricalEquivalence
