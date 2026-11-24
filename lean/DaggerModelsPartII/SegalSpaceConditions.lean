import DaggerModelsPartII.DiagramMappingSpace
import DaggerModelsPartII.SegalLocalizers
import TopCatModelCategory.ModelCategorySSet

/-! The strict Segal and unitary completeness mapping conditions of Part II. -/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.SegalLocalizers

/-- The Segal mapping condition at every spine in dimension at least two. -/
def segalCondition (W : ReverseDaggerSpace.{u}) : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    weakEquivalences SSet.{u} (diagramMappingPrecomp (segalMap n) W)

/-- Completeness tested by the actual walking unitary and its selected zero vertex. -/
def unitaryCompletenessCondition (W : ReverseDaggerSpace.{u}) : Prop :=
  weakEquivalences SSet.{u} (diagramMappingPrecomp unitaryCompletenessMap W)

/-- The two strict mapping conditions in `h1.def.segal-complete`.
The injective fibrancy hypothesis is imposed separately when interpreting this
as a unitarily complete dagger Segal space. -/
def unitarilyCompleteSegalCondition (W : ReverseDaggerSpace.{u}) : Prop :=
  segalCondition W ∧ unitaryCompletenessCondition W

/-- Passing the two displayed mapping tests is exactly passing the literal family. -/
theorem unitarilyCompleteSegalCondition_iff_family (W : ReverseDaggerSpace.{u}) :
    unitarilyCompleteSegalCondition W ↔
      localizingFamily ≤ fun _ _ f ↦
        weakEquivalences SSet.{u} (diagramMappingPrecomp f W) := by
  constructor
  · rintro ⟨hSegal, hComplete⟩ A B f hf
    obtain ⟨i⟩ := hf
    cases i with
    | inl n => exact hSegal n n.2
    | inr i => exact hComplete
  · intro h
    constructor
    · intro n hn
      have hi := ofHoms.mk (f := fun i : LocalizerIndex ↦ (localizerMap.{u} i).2.2)
        (Sum.inl ⟨n, hn⟩)
      exact h (segalMap.{u} n) hi
    · have hi := ofHoms.mk (f := fun i : LocalizerIndex ↦ (localizerMap.{u} i).2.2)
        (Sum.inr ())
      exact h unitaryCompletenessMap.{u} hi

end DaggerModels.PartII.SegalLocalizers
