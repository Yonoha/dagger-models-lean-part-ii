import DaggerModelsPartII.ProjectiveSimplicialAxiom
import DaggerModelsPartII.ProjectiveLocalizationModel
import DaggerModelsPartII.LocalizedInjectiveSimplicial
import DaggerModelsPartII.SegalLocalizationModels
import DaggerModelsPartII.ActualSegalLocalization

/-!
# Simplicial pushout-product after projective localization

The projective cofibration part comes from the base projective SM7 theorem.
The local weak-equivalence part uses equality of projective and injective
local weak classes and the established injective local mapping argument.
-/

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory MorphismProperty HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.ProjectiveKanDiagram

variable (C : Type u) [Category.{u} C]

noncomputable section

local instance projectiveLocalizedSimplicialBase : ModelCategory (C ⥤ SSet.{u}) :=
  modelCategory C

/-- SM7 for any model on simplicial-set diagrams with the exact projective
cofibrations and projective local weak-equivalence class. -/
theorem localizedModel_pushoutProduct_sm7
    (S : MorphismProperty (C ⥤ SSet.{u}))
    (N : ModelCategory (C ⥤ SSet.{u}))
    (hcof : N.categoryWithCofibrations.cofibrations =
      (modelCategory C).categoryWithCofibrations.cofibrations)
    (hweak : N.categoryWithWeakEquivalences.weakEquivalences =
      @Localization.localEquivalences (C ⥤ SSet.{u}) _ (modelCategory C) _ _ S)
    {A B : C ⥤ SSet.{u}} (i : A ⟶ B)
    {K L : SSet.{u}} (j : K ⟶ L)
    (hi : N.categoryWithCofibrations.cofibrations i)
    (hj : HomotopicalAlgebra.cofibrations SSet.{u} j)
    (sq : Functor.PushoutObjObj (InjectiveKanDiagram.curriedDiagramTensor C) i j) :
    N.categoryWithCofibrations.cofibrations sq.ι ∧
      ((N.categoryWithWeakEquivalences.weakEquivalences i ∨
          HomotopicalAlgebra.weakEquivalences SSet.{u} j) →
        N.categoryWithWeakEquivalences.weakEquivalences sq.ι) := by
  have hbi : (modelCategory C).categoryWithCofibrations.cofibrations i := by
    rw [← hcof]
    exact hi
  haveI : Mono i := by
    have hmono := boundaryCofibrations_levelwiseMono C i hbi
    exact (NatTrans.mono_iff_mono_app i).mpr hmono
  haveI : Mono j :=
    (SSet.modelCategoryQuillen.cofibration_iff j).mp ((cofibration_iff j).mpr hj)
  refine ⟨?_, ?_⟩
  · rw [hcof]
    exact model_pushoutProduct_cofibration C i j hbi hj sq
  · rintro (hwi | hwj)
    · rw [hweak] at hwi ⊢
      have hInj : (letI := InjectiveKanDiagram.modelCategory C;
          Localization.localEquivalences S i) := by
        rw [← ProjectiveInjectiveComparison.localEquivalences_eq C S]
        exact hwi
      have hInjBox := InjectiveKanDiagram.localEquivalences_pushoutProduct
        C S i j hInj sq
      rw [ProjectiveInjectiveComparison.localEquivalences_eq C S]
      exact hInjBox
    · rw [hweak]
      have hbase := (model_pushoutProduct_sm7 C i j hbi hj sq).2 (Or.inr hwj)
      change (letI := modelCategory C; Localization.localEquivalences S sq.ι)
      letI : ModelCategory (C ⥤ SSet.{u}) := modelCategory C
      exact Localization.weakEquivalences_le_localEquivalences S sq.ι hbase

/-- The actual localized projective model at a small monomorphism family
satisfies simplicial pushout-product SM7. -/
theorem localized_pushoutProduct_sm7
    (I : Type u) (s : I → Arrow (C ⥤ SSet.{u}))
    (hs : ∀ k, Mono (s k).hom)
    {A B : C ⥤ SSet.{u}} (i : A ⟶ B)
    {K L : SSet.{u}} (j : K ⟶ L)
    (hi : (localizedModelCategory C I s hs).categoryWithCofibrations.cofibrations i)
    (hj : HomotopicalAlgebra.cofibrations SSet.{u} j)
    (sq : Functor.PushoutObjObj (InjectiveKanDiagram.curriedDiagramTensor C) i j) :
    (localizedModelCategory C I s hs).categoryWithCofibrations.cofibrations sq.ι ∧
      (((localizedModelCategory C I s hs).categoryWithWeakEquivalences.weakEquivalences i ∨
          HomotopicalAlgebra.weakEquivalences SSet.{u} j) →
        (localizedModelCategory C I s hs).categoryWithWeakEquivalences.weakEquivalences sq.ι) := by
  have he := localized_exactClasses C I s hs
  exact localizedModel_pushoutProduct_sm7 C
    (InjectiveKanDiagram.diagramLocalizingFamily C I s)
    (localizedModelCategory C I s hs) he.1 he.2 i j hi hj sq

end

end DaggerModels.PartII.ProjectiveKanDiagram

namespace DaggerModels.PartII.SegalLocalizers

noncomputable section

/-- Simplicial SM7 for the localized projective model on the actual reversal
index and manuscript Segal localizers. -/
theorem projectiveSegalModel_pushoutProduct_sm7
    {A B : ReverseDaggerSpace.{0}} (i : A ⟶ B)
    {K L : SSet.{0}} (j : K ⟶ L)
    (hi : projectiveSegalModel.categoryWithCofibrations.cofibrations i)
    (hj : HomotopicalAlgebra.cofibrations SSet.{0} j)
    (sq : Functor.PushoutObjObj
      (InjectiveKanDiagram.curriedDiagramTensor ReverseSimplexᵒᵖ) i j) :
    projectiveSegalModel.categoryWithCofibrations.cofibrations sq.ι ∧
      ((projectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences i ∨
          HomotopicalAlgebra.weakEquivalences SSet.{0} j) →
        projectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences sq.ι) :=
  ProjectiveKanDiagram.localized_pushoutProduct_sm7 ReverseSimplexᵒᵖ LocalizerIndex
    localizerArrow localizerArrow_mono i j hi hj sq

end

end DaggerModels.PartII.SegalLocalizers

namespace DaggerModels.PartII.ActualIndexProjectiveModel

open DaggerModels.PartII.DaggerSimplexPartIIndex
open DaggerModels.PartII.SegalLocalizers

noncomputable section

/-- Simplicial SM7 for the localized projective model on the actual Part I
free dagger-simplex index. -/
theorem actualSegalModel_pushoutProduct_sm7
    {A B : ActualSpace} (i : A ⟶ B)
    {K L : SSet.{0}} (j : K ⟶ L)
    (hi : actualSegalModel.categoryWithCofibrations.cofibrations i)
    (hj : HomotopicalAlgebra.cofibrations SSet.{0} j)
    (sq : Functor.PushoutObjObj
      (InjectiveKanDiagram.curriedDiagramTensor ActualDaggerSimplexᵒᵖ) i j) :
    actualSegalModel.categoryWithCofibrations.cofibrations sq.ι ∧
      ((actualSegalModel.categoryWithWeakEquivalences.weakEquivalences i ∨
          HomotopicalAlgebra.weakEquivalences SSet.{0} j) →
        actualSegalModel.categoryWithWeakEquivalences.weakEquivalences sq.ι) :=
  ProjectiveKanDiagram.localized_pushoutProduct_sm7 ActualDaggerSimplexᵒᵖ LocalizerIndex
    actualImageLocalizer actualImageLocalizer_mono i j hi hj sq

end

end DaggerModels.PartII.ActualIndexProjectiveModel
