import DaggerModelsPartII.ProjectiveLocalizationModel
import DaggerModelsPartII.MappingCofibrationInclusion

/-!
# Identity Quillen equivalence between local diagram models

At the same small monomorphism family, projective and injective localizations
have the same local weak equivalences. Their cofibrations remain the original
projective and injective classes, respectively.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII

noncomputable section

/-- The identity functor is a Quillen equivalence from the projective to the
injective localization at the same small monomorphism family. -/
theorem localizedIdentity_isQuillenEquivalence
    (C : Type u) [Category.{u} C] (I : Type u)
    (s : I → Arrow (C ⥤ SSet.{u})) (hs : ∀ i, Mono (s i).hom) :
    @Adjunction.IsQuillenEquivalence (C ⥤ SSet.{u}) (C ⥤ SSet.{u}) _ _
      (ProjectiveKanDiagram.localizedModelCategory C I s hs)
      (InjectiveKanDiagram.localizedModelCategory C I s hs)
      (𝟭 _) (𝟭 _) Adjunction.id := by
  let P := ProjectiveKanDiagram.localizedModelCategory C I s hs
  let N := InjectiveKanDiagram.localizedModelCategory C I s hs
  have hp := ProjectiveKanDiagram.localized_exactClasses C I s hs
  have hn := InjectiveKanDiagram.localized_exactClasses C I s hs
  have hc : P.categoryWithCofibrations.cofibrations ≤
      N.categoryWithCofibrations.cofibrations := by
    rw [hp.1, hn.1]
    exact ProjectiveInjectiveComparison.cofibrations_le C
  have hw : P.categoryWithWeakEquivalences.weakEquivalences =
      N.categoryWithWeakEquivalences.weakEquivalences := by
    rw [hp.2, hn.2]
    exact ProjectiveInjectiveComparison.localEquivalences_eq C
      (InjectiveKanDiagram.diagramLocalizingFamily C I s)
  exact identity_isQuillenEquivalence_of_cofibrations_le P N hc hw

end

end DaggerModels.PartII
