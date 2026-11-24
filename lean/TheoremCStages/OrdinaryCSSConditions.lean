import OrdinaryCSSLocalization
import DaggerModelsPartII.InjectiveKanModel

/-!
# Strict ordinary complete-Segal-space mapping conditions

The generic injective theorem `model_homotopyMapping_iff_strict` computes
the derived local tests on an injectively fibrant target. This identifies
the exact ordinary spine and walking-isomorphism mapping conditions for
the already checked ordinary CSS localization, without any dagger input.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryCSSConditions

open OrdinaryCSSLocalization

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- The strict ordinary Segal mapping tests in all dimensions at least two. -/
def segalCondition (W : Space) : Prop :=
  ∀ n : ℕ, 2 ≤ n → weakEquivalences SSet.{0}
    (diagramMappingPrecomp (spineMap n) W)

/-- The strict ordinary walking-isomorphism completeness mapping test. -/
def completenessCondition (W : Space) : Prop :=
  weakEquivalences SSet.{0} (diagramMappingPrecomp completenessMap W)

/-- The ordinary conditions associated to the exact chosen localization family. -/
def completeSegalCondition (W : Space) : Prop :=
  segalCondition W ∧ completenessCondition W

/-- The two displayed strict conditions test exactly the registered ordinary family. -/
theorem completeSegalCondition_iff_family (W : Space) :
    completeSegalCondition W ↔
      localizingFamily ≤ fun _ _ f ↦
        weakEquivalences SSet.{0} (diagramMappingPrecomp f W) := by
  constructor
  · rintro ⟨hS, hC⟩ A B f hf
    obtain ⟨i⟩ := hf
    cases i with
    | inl n => exact hS n n.2
    | inr _ => exact hC
  · intro h
    constructor
    · intro n hn
      exact h (spineMap n) (ofHoms.mk
        (f := fun i : LocalizerIndex ↦ (localizerArrow i).hom) (.inl ⟨n, hn⟩))
    · exact h completenessMap (ofHoms.mk
        (f := fun i : LocalizerIndex ↦ (localizerArrow i).hom) (.inr ()))

/-- On the injective base model, local objects are exactly fibrant targets
satisfying the literal strict ordinary Segal and completeness conditions. -/
theorem localObject_iff_strict (W : Space) :
    Localization.localObject localizingFamily W ↔
      IsFibrant W ∧ completeSegalCondition W := by
  constructor
  · rintro ⟨hW, h⟩
    letI := hW
    refine ⟨hW, (completeSegalCondition_iff_family W).mpr ?_⟩
    intro A B f hf
    exact (InjectiveKanDiagram.model_homotopyMapping_iff_strict
      SimplexCategoryᵒᵖ f).mp (h f hf)
  · rintro ⟨hW, h⟩
    letI := hW
    refine ⟨hW, ?_⟩
    intro A B f hf
    exact (InjectiveKanDiagram.model_homotopyMapping_iff_strict
      SimplexCategoryᵒᵖ f).mpr
        ((completeSegalCondition_iff_family W).mp h f hf)

/-- Fibrancy in the actual ordinary CSS localization has the strict mapping description. -/
theorem isFibrant_iff (W : Space) :
    @IsFibrant Space _ OrdinaryCSSLocalization.model.categoryWithFibrations _ W ↔
      IsFibrant W ∧ completeSegalCondition W :=
  (OrdinaryCSSLocalization.isFibrant_iff W).trans (localObject_iff_strict W)

#print axioms completeSegalCondition_iff_family
#print axioms localObject_iff_strict
#print axioms isFibrant_iff

end

end DaggerModels.PartII.OrdinaryCSSConditions
