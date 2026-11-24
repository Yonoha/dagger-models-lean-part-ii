import OrdinaryCSSConditions

/-!
# The ordinary Segal-space localization before completeness

Apply the existing injective localization construction to the literal ordinary
spine inclusions only. Fibrant objects are precisely injectively Kan fibrant
ordinary simplicial spaces satisfying the existing strict Segal condition.
The selected walking-isomorphism completeness map is not part of this family.
This is the Segal model used in Rezk Sections 10--14, not a replacement for the
fixed ordinary CSS model or for the original Theorem C statement.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory HomotopicalAlgebra MorphismProperty Simplicial
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalLocalization

open OrdinaryCSSLocalization (Space spineMap spineMap_mono)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- The ordinary Segal localizers contain exactly the chosen spine inclusions. -/
abbrev LocalizerIndex := {n : ℕ // 2 ≤ n}

def localizerArrow (n : LocalizerIndex) : Arrow Space := Arrow.mk (spineMap n)

theorem localizerArrow_mono (n : LocalizerIndex) : Mono (localizerArrow n).hom :=
  spineMap_mono n

/-- The exact small family of ordinary horizontal spine maps. -/
def localizingFamily : MorphismProperty Space :=
  InjectiveKanDiagram.diagramLocalizingFamily SimplexCategoryᵒᵖ
    LocalizerIndex localizerArrow

/-- The existing injective localization construction applied to spines alone. -/
def model : ModelCategory Space :=
  InjectiveKanDiagram.localizedModelCategory SimplexCategoryᵒᵖ
    LocalizerIndex localizerArrow localizerArrow_mono

/-- Cofibrations are the original injective cofibrations; weak maps are spine-local maps. -/
theorem exactClasses :
    model.categoryWithCofibrations.cofibrations =
      (InjectiveKanDiagram.modelCategory
        SimplexCategoryᵒᵖ).categoryWithCofibrations.cofibrations ∧
    model.categoryWithWeakEquivalences.weakEquivalences =
      Localization.localEquivalences localizingFamily :=
  InjectiveKanDiagram.localized_exactClasses SimplexCategoryᵒᵖ
    LocalizerIndex localizerArrow localizerArrow_mono

/-- The same strict Segal tests quantify over exactly this small family. -/
theorem segalCondition_iff_family (W : Space) :
    OrdinaryCSSConditions.segalCondition W ↔
      localizingFamily ≤ fun _ _ f ↦
        weakEquivalences SSet.{0} (diagramMappingPrecomp f W) := by
  constructor
  · intro h A B f hf
    obtain ⟨n⟩ := hf
    exact h n n.2
  · intro h n hn
    exact h (spineMap n) (ofHoms.mk
      (f := fun i : LocalizerIndex ↦ (localizerArrow i).hom) ⟨n, hn⟩)

/-- Derived spine-locality agrees with strict Segal tests on the actual fibrant target. -/
theorem localObject_iff_strict (W : Space) :
    Localization.localObject localizingFamily W ↔
      IsFibrant W ∧ OrdinaryCSSConditions.segalCondition W := by
  constructor
  · rintro ⟨hW, h⟩
    have := hW
    refine ⟨hW, (segalCondition_iff_family W).mpr ?_⟩
    intro A B f hf
    exact (InjectiveKanDiagram.model_homotopyMapping_iff_strict
      SimplexCategoryᵒᵖ f).mp (h f hf)
  · rintro ⟨hW, h⟩
    have := hW
    refine ⟨hW, ?_⟩
    intro A B f hf
    exact (InjectiveKanDiagram.model_homotopyMapping_iff_strict
      SimplexCategoryᵒᵖ f).mpr ((segalCondition_iff_family W).mp h f hf)

/-- The ordinary Segal fibrant objects require no ordinary completeness premise. -/
theorem isFibrant_iff (W : Space) :
    @IsFibrant Space _ model.categoryWithFibrations _ W ↔
      IsFibrant W ∧ OrdinaryCSSConditions.segalCondition W :=
  (InjectiveKanDiagram.localized_isFibrant_iff SimplexCategoryᵒᵖ
    LocalizerIndex localizerArrow localizerArrow_mono W).trans (localObject_iff_strict W)

/-- Each of the original spine inclusions is weak in the actual Segal model. -/
theorem spineMap_weak (n : ℕ) (hn : 2 ≤ n) :
    model.categoryWithWeakEquivalences.weakEquivalences (spineMap n) := by
  rw [exactClasses.2]
  apply Localization.family_le_localEquivalences localizingFamily
  exact ofHoms.mk
    (f := fun i : LocalizerIndex ↦ (localizerArrow i).hom) ⟨n, hn⟩

#print axioms model
#print axioms exactClasses
#print axioms localObject_iff_strict
#print axioms isFibrant_iff
#print axioms spineMap_weak

end

end DaggerModels.PartII.OrdinarySegalLocalization
