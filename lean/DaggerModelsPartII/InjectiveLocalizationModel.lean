import DaggerModelsPartII.InjectiveLocalReplacement
import DaggerModelsPartII.InjectiveLocalizationSmith
import DaggerModelsPartII.ProjectiveWeakAccessibility
import DaggerModelsPartII.ProjectiveInjectiveComparison
import DaggerModelsPartII.LocalizationModelProper
import DaggerModelsPartII.LocalizationModelFibrancy

/-!
# Localized injective Kan diagram model

An accessible local replacement gives a solution set for the exact local weak
class. Smith recognition then supplies the injective left localization.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.InjectiveKanDiagram

noncomputable section

variable (C : Type u) [Category.{u} C]

local instance injectiveLocalizationBaseModel : ModelCategory (C ⥤ SSet.{u}) := modelCategory C

private theorem weakArrow_isAccessible :
    IsAccessibleCategory.{u}
      (DaggerAccessibleSolutions.arrowProperty
        (HomotopicalAlgebra.weakEquivalences (C ⥤ SSet.{u}))).FullSubcategory := by
  have h := ProjectiveKanDiagram.weakArrow_isAccessible C
  simpa only [InjectiveKanDiagram.model_weakEquivalences,
    ProjectiveKanDiagram.weakEquivalences] using h

private theorem weakArrow_inclusion_isAccessible :
    Functor.IsAccessible.{u}
      (DaggerAccessibleSolutions.arrowProperty
        (HomotopicalAlgebra.weakEquivalences (C ⥤ SSet.{u}))).ι := by
  have h := ProjectiveKanDiagram.weakArrow_inclusion_isAccessible C
  simpa only [InjectiveKanDiagram.model_weakEquivalences,
    ProjectiveKanDiagram.weakEquivalences] using h

/-- The exact local weak class has a Smith solution set, given the local
weak-equivalence property of the replacement unit. -/
def localSolutionSetOfUnit (I : Type u) (s : I → Arrow (C ⥤ SSet.{u}))
    (hs : ∀ i, Mono (s i).hom)
    (hUnit : ∀ X, Localization.localEquivalences (diagramLocalizingFamily C I s)
      ((localReplacementUnit C I s).app X)) :
    DaggerSmithSolutionSet.SolutionData.{u} (quotientSubobjectGenerators C)
      (Localization.localEquivalences (diagramLocalizingFamily C I s)) := by
  letI := ProjectiveKanDiagram.locallyPresentable C
  exact Localization.localReplacementSolutionSet
    (diagramLocalizingFamily C I s) (quotientSubobjectGenerators C)
    (localReplacement C I s) (localReplacementUnit C I s)
    (localReplacement_isLocal C I s hs) hUnit
    (localReplacement_accessible C I s)
    (weakArrow_isAccessible C) (weakArrow_inclusion_isAccessible C)

/-- Smith data for injective localization, conditional only on the replacement
unit being locally weak. -/
def localizedCombinatorialDataOfUnit (I : Type u) (s : I → Arrow (C ⥤ SSet.{u}))
    (hs : ∀ i, Mono (s i).hom)
    (hUnit : ∀ X, Localization.localEquivalences (diagramLocalizingFamily C I s)
      ((localReplacementUnit C I s).app X)) :
    DaggerSmithSolutionSet.CombinatorialData (localSolutionSetOfUnit C I s hs hUnit) :=
  localizationSmithData C (diagramLocalizingFamily C I s)
    (localSolutionSetOfUnit C I s hs hUnit)

/-- The injective localization model produced by the conditional Smith data. -/
def localizedModelCategoryOfUnit (I : Type u) (s : I → Arrow (C ⥤ SSet.{u}))
    (hs : ∀ i, Mono (s i).hom)
    (hUnit : ∀ X, Localization.localEquivalences (diagramLocalizingFamily C I s)
      ((localReplacementUnit C I s).app X)) :
    ModelCategory (C ⥤ SSet.{u}) :=
  (localizedCombinatorialDataOfUnit C I s hs hUnit).model

/-- The Smith model has precisely injective cofibrations and the prescribed
derived local weak equivalences. -/
theorem localized_exactClassesOfUnit (I : Type u) (s : I → Arrow (C ⥤ SSet.{u}))
    (hs : ∀ i, Mono (s i).hom)
    (hUnit : ∀ X, Localization.localEquivalences (diagramLocalizingFamily C I s)
      ((localReplacementUnit C I s).app X)) :
    (localizedModelCategoryOfUnit C I s hs hUnit).categoryWithCofibrations.cofibrations =
      (modelCategory C).categoryWithCofibrations.cofibrations ∧
    (localizedModelCategoryOfUnit C I s hs hUnit).categoryWithWeakEquivalences.weakEquivalences =
      Localization.localEquivalences (diagramLocalizingFamily C I s) := by
  let d := localizedCombinatorialDataOfUnit C I s hs hUnit
  have hcof : d.model.categoryWithCofibrations.cofibrations =
      (modelCategory C).categoryWithCofibrations.cofibrations := by
    exact d.modelCof
  exact ⟨hcof, d.modelWeak⟩

/-- The Smith model inherits left properness from the injective Kan diagram model. -/
theorem localized_leftProperOfUnit (I : Type u) (s : I → Arrow (C ⥤ SSet.{u}))
    (hs : ∀ i, Mono (s i).hom)
    (hUnit : ∀ X, Localization.localEquivalences (diagramLocalizingFamily C I s)
      ((localReplacementUnit C I s).app X))
    {A B D P : C ⥤ SSet.{u}} {i : A ⟶ B} {k : A ⟶ D}
    {l : B ⟶ P} {r : D ⟶ P} (sq : IsPushout i k l r)
    (hi : (localizedModelCategoryOfUnit C I s hs hUnit).categoryWithCofibrations.cofibrations i)
    (hk :
      (localizedModelCategoryOfUnit C I s hs hUnit).categoryWithWeakEquivalences.weakEquivalences k) :
    (localizedModelCategoryOfUnit C I s hs hUnit).categoryWithWeakEquivalences.weakEquivalences l :=
      by
  let d := localizedCombinatorialDataOfUnit C I s hs hUnit
  have he := localized_exactClassesOfUnit C I s hs hUnit
  exact Localization.localizedModel_leftProper
    (fun sq hi hw ↦ model_leftProper C sq hi hw)
    (diagramLocalizingFamily C I s) d.model he.1 he.2 sq.flip hk hi

/-- The exact local weak class of a small monomorphism family has a Smith
solution set. -/
def localSolutionSet (I : Type u) (s : I → Arrow (C ⥤ SSet.{u}))
    (hs : ∀ i, Mono (s i).hom) :
    DaggerSmithSolutionSet.SolutionData.{u} (quotientSubobjectGenerators C)
      (Localization.localEquivalences (diagramLocalizingFamily C I s)) :=
  localSolutionSetOfUnit C I s hs (localReplacementUnit_localEquivalence C I s hs)

/-- Combinatorial Smith data for the injective localization at a small
monomorphism family. -/
def localizedCombinatorialData (I : Type u) (s : I → Arrow (C ⥤ SSet.{u}))
    (hs : ∀ i, Mono (s i).hom) :
    DaggerSmithSolutionSet.CombinatorialData (localSolutionSet C I s hs) :=
  localizedCombinatorialDataOfUnit C I s hs
    (localReplacementUnit_localEquivalence C I s hs)

/-- The localized injective Kan diagram model. -/
def localizedModelCategory (I : Type u) (s : I → Arrow (C ⥤ SSet.{u}))
    (hs : ∀ i, Mono (s i).hom) : ModelCategory (C ⥤ SSet.{u}) :=
  (localizedCombinatorialData C I s hs).model

/-- Its cofibrations are exactly the original injective cofibrations, and its
weak equivalences are exactly the derived local equivalences. -/
theorem localized_exactClasses (I : Type u) (s : I → Arrow (C ⥤ SSet.{u}))
    (hs : ∀ i, Mono (s i).hom) :
    (localizedModelCategory C I s hs).categoryWithCofibrations.cofibrations =
      (modelCategory C).categoryWithCofibrations.cofibrations ∧
    (localizedModelCategory C I s hs).categoryWithWeakEquivalences.weakEquivalences =
      Localization.localEquivalences (diagramLocalizingFamily C I s) :=
  localized_exactClassesOfUnit C I s hs
    (localReplacementUnit_localEquivalence C I s hs)

/-- The localized injective model is left proper. -/
theorem localized_leftProper (I : Type u) (s : I → Arrow (C ⥤ SSet.{u}))
    (hs : ∀ i, Mono (s i).hom)
    {A B D P : C ⥤ SSet.{u}} {i : A ⟶ B} {k : A ⟶ D}
    {l : B ⟶ P} {r : D ⟶ P} (sq : IsPushout i k l r)
    (hi : (localizedModelCategory C I s hs).categoryWithCofibrations.cofibrations i)
    (hk : (localizedModelCategory C I s hs).categoryWithWeakEquivalences.weakEquivalences k) :
    (localizedModelCategory C I s hs).categoryWithWeakEquivalences.weakEquivalences l :=
  localized_leftProperOfUnit C I s hs
    (localReplacementUnit_localEquivalence C I s hs) sq hi hk

/-- Fibrant objects of the localized injective model are precisely injectively
fibrant local objects for the specified family. -/
theorem localized_isFibrant_iff (I : Type u) (s : I → Arrow (C ⥤ SSet.{u}))
    (hs : ∀ i, Mono (s i).hom) (W : C ⥤ SSet.{u}) :
    @IsFibrant (C ⥤ SSet.{u}) _
      (localizedModelCategory C I s hs).categoryWithFibrations _ W ↔
    Localization.localObject (diagramLocalizingFamily C I s) W := by
  have he := localized_exactClasses C I s hs
  exact Localization.localized_isFibrant_iff (N := localizedModelCategory C I s hs)
    (modelCategory C)
    (diagramLocalizingFamily C I s) he.1 he.2 W

end

end DaggerModels.PartII.InjectiveKanDiagram
