import DaggerModelsPartII.InjectiveLocalizationModel
import DaggerModelsPartII.ProjectiveLocalizationSmith

/-!
# Localized projective Kan diagram model

The injective local replacement also detects the projective local weak class,
since the two base diagram models have the same local equivalences. Smith
recognition then supplies the projective left localization.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.ProjectiveKanDiagram

noncomputable section

variable (C : Type u) [Category.{u} C]

local instance projectiveLocalizationBaseModel : ModelCategory (C ⥤ SSet.{u}) := modelCategory C

/-- The exact projective local weak class has a Smith solution set, given the
local weak-equivalence property of the injective replacement unit. -/
def localSolutionSetOfUnit (I : Type u) (s : I → Arrow (C ⥤ SSet.{u}))
    (hs : ∀ i, Mono (s i).hom)
    (hUnit : ∀ X,
      (letI := InjectiveKanDiagram.modelCategory C;
        Localization.localEquivalences (InjectiveKanDiagram.diagramLocalizingFamily C I s)
          ((InjectiveKanDiagram.localReplacementUnit C I s).app X))) :
    DaggerSmithSolutionSet.SolutionData.{u} (boundaryGenerators C)
      (Localization.localEquivalences (InjectiveKanDiagram.diagramLocalizingFamily C I s)) := by
  let S := InjectiveKanDiagram.diagramLocalizingFamily C I s
  let R := InjectiveKanDiagram.localReplacement C I s
  let η := InjectiveKanDiagram.localReplacementUnit C I s
  letI := locallyPresentable C
  have hR : ∀ X, Localization.localObject S (R.obj X) := by
    intro X
    have hInj := InjectiveKanDiagram.localReplacement_isLocal C I s hs X
    exact (ProjectiveInjectiveComparison.localObject_iff_on_injectiveFibrant
      C S _ hInj.1).mpr hInj
  have hη : ∀ X, Localization.localEquivalences S (η.app X) := by
    intro X
    have heq := ProjectiveInjectiveComparison.localEquivalences_eq C S
    exact heq.symm ▸ hUnit X
  exact Localization.localReplacementSolutionSet S (boundaryGenerators C) R η
    hR hη (InjectiveKanDiagram.localReplacement_accessible C I s)
    (by simpa only [model_weakEquivalences] using weakArrow_isAccessible C)
    (by simpa only [model_weakEquivalences] using weakArrow_inclusion_isAccessible C)

/-- Projective Smith data for the exact derived local weak class. -/
def localizedCombinatorialDataOfUnit (I : Type u) (s : I → Arrow (C ⥤ SSet.{u}))
    (hs : ∀ i, Mono (s i).hom)
    (hUnit : ∀ X,
      (letI := InjectiveKanDiagram.modelCategory C;
        Localization.localEquivalences (InjectiveKanDiagram.diagramLocalizingFamily C I s)
          ((InjectiveKanDiagram.localReplacementUnit C I s).app X))) :
    DaggerSmithSolutionSet.CombinatorialData (localSolutionSetOfUnit C I s hs hUnit) :=
  localizationSmithData C (InjectiveKanDiagram.diagramLocalizingFamily C I s)
    (localSolutionSetOfUnit C I s hs hUnit)

/-- The projective localization model produced by the conditional Smith data. -/
def localizedModelCategoryOfUnit (I : Type u) (s : I → Arrow (C ⥤ SSet.{u}))
    (hs : ∀ i, Mono (s i).hom)
    (hUnit : ∀ X,
      (letI := InjectiveKanDiagram.modelCategory C;
        Localization.localEquivalences (InjectiveKanDiagram.diagramLocalizingFamily C I s)
          ((InjectiveKanDiagram.localReplacementUnit C I s).app X))) :
    ModelCategory (C ⥤ SSet.{u}) :=
  (localizedCombinatorialDataOfUnit C I s hs hUnit).model

/-- The projective Smith model has precisely the original projective
cofibrations and the derived local weak-equivalence class. -/
theorem localized_exactClassesOfUnit (I : Type u) (s : I → Arrow (C ⥤ SSet.{u}))
    (hs : ∀ i, Mono (s i).hom)
    (hUnit : ∀ X,
      (letI := InjectiveKanDiagram.modelCategory C;
        Localization.localEquivalences (InjectiveKanDiagram.diagramLocalizingFamily C I s)
          ((InjectiveKanDiagram.localReplacementUnit C I s).app X))) :
    (localizedModelCategoryOfUnit C I s hs hUnit).categoryWithCofibrations.cofibrations =
      (modelCategory C).categoryWithCofibrations.cofibrations ∧
    (localizedModelCategoryOfUnit C I s hs hUnit).categoryWithWeakEquivalences.weakEquivalences =
      Localization.localEquivalences (InjectiveKanDiagram.diagramLocalizingFamily C I s) :=
  localizationSmith_exactClasses C (InjectiveKanDiagram.diagramLocalizingFamily C I s)
    (localSolutionSetOfUnit C I s hs hUnit)

/-- The projective Smith model inherits left properness from the projective
Kan diagram model. -/
theorem localized_leftProperOfUnit (I : Type u) (s : I → Arrow (C ⥤ SSet.{u}))
    (hs : ∀ i, Mono (s i).hom)
    (hUnit : ∀ X,
      (letI := InjectiveKanDiagram.modelCategory C;
        Localization.localEquivalences (InjectiveKanDiagram.diagramLocalizingFamily C I s)
          ((InjectiveKanDiagram.localReplacementUnit C I s).app X)))
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
    (InjectiveKanDiagram.diagramLocalizingFamily C I s) d.model he.1 he.2 sq.flip hk hi

/-- The exact projective local weak class of a small monomorphism family has
a Smith solution set. -/
def localSolutionSet (I : Type u) (s : I → Arrow (C ⥤ SSet.{u}))
    (hs : ∀ i, Mono (s i).hom) :
    DaggerSmithSolutionSet.SolutionData.{u} (boundaryGenerators C)
      (Localization.localEquivalences (InjectiveKanDiagram.diagramLocalizingFamily C I s)) :=
  localSolutionSetOfUnit C I s hs
    (InjectiveKanDiagram.localReplacementUnit_localEquivalence C I s hs)

/-- Combinatorial Smith data for the projective localization. -/
def localizedCombinatorialData (I : Type u) (s : I → Arrow (C ⥤ SSet.{u}))
    (hs : ∀ i, Mono (s i).hom) :
    DaggerSmithSolutionSet.CombinatorialData (localSolutionSet C I s hs) :=
  localizedCombinatorialDataOfUnit C I s hs
    (InjectiveKanDiagram.localReplacementUnit_localEquivalence C I s hs)

/-- The localized projective Kan diagram model. -/
def localizedModelCategory (I : Type u) (s : I → Arrow (C ⥤ SSet.{u}))
    (hs : ∀ i, Mono (s i).hom) : ModelCategory (C ⥤ SSet.{u}) :=
  (localizedCombinatorialData C I s hs).model

/-- The localized cofibrations are the original projective cofibrations, and
the weak equivalences are the exact derived local weak equivalences. -/
theorem localized_exactClasses (I : Type u) (s : I → Arrow (C ⥤ SSet.{u}))
    (hs : ∀ i, Mono (s i).hom) :
    (localizedModelCategory C I s hs).categoryWithCofibrations.cofibrations =
      (modelCategory C).categoryWithCofibrations.cofibrations ∧
    (localizedModelCategory C I s hs).categoryWithWeakEquivalences.weakEquivalences =
      Localization.localEquivalences (InjectiveKanDiagram.diagramLocalizingFamily C I s) :=
  localized_exactClassesOfUnit C I s hs
    (InjectiveKanDiagram.localReplacementUnit_localEquivalence C I s hs)

/-- The localized projective model is left proper. -/
theorem localized_leftProper (I : Type u) (s : I → Arrow (C ⥤ SSet.{u}))
    (hs : ∀ i, Mono (s i).hom)
    {A B D P : C ⥤ SSet.{u}} {i : A ⟶ B} {k : A ⟶ D}
    {l : B ⟶ P} {r : D ⟶ P} (sq : IsPushout i k l r)
    (hi : (localizedModelCategory C I s hs).categoryWithCofibrations.cofibrations i)
    (hk : (localizedModelCategory C I s hs).categoryWithWeakEquivalences.weakEquivalences k) :
    (localizedModelCategory C I s hs).categoryWithWeakEquivalences.weakEquivalences l :=
  localized_leftProperOfUnit C I s hs
    (InjectiveKanDiagram.localReplacementUnit_localEquivalence C I s hs) sq hi hk

/-- Fibrant objects of the localized projective model are precisely
projectively fibrant local objects for the specified family. -/
theorem localized_isFibrant_iff (I : Type u) (s : I → Arrow (C ⥤ SSet.{u}))
    (hs : ∀ i, Mono (s i).hom) (W : C ⥤ SSet.{u}) :
    @IsFibrant (C ⥤ SSet.{u}) _
      (localizedModelCategory C I s hs).categoryWithFibrations _ W ↔
    Localization.localObject (InjectiveKanDiagram.diagramLocalizingFamily C I s) W := by
  have he := localized_exactClasses C I s hs
  exact Localization.localized_isFibrant_iff (N := localizedModelCategory C I s hs)
    (modelCategory C) (InjectiveKanDiagram.diagramLocalizingFamily C I s) he.1 he.2 W

end

end DaggerModels.PartII.ProjectiveKanDiagram
