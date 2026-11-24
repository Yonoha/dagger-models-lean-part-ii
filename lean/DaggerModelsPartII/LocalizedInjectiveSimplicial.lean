import DaggerModelsPartII.LocalizingBoundaryLocality
import DaggerModelsPartII.LocalEquivalenceClasses
import DaggerModelsPartII.InjectiveLocalizationModel

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory MorphismProperty HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerModels.PartII.InjectiveKanDiagram
variable (C : Type u) [Category.{u} C]
noncomputable section

local instance baseModel : ModelCategory (C ⥤ SSet.{u}) := modelCategory C

/-- Local equivalences are preserved by the diagram pushout-product with a
simplicial monomorphism. -/
theorem localEquivalences_pushoutProduct
    (S : MorphismProperty (C ⥤ SSet.{u}))
    {A B : C ⥤ SSet.{u}} (i : A ⟶ B)
    {K L : SSet.{u}} (j : K ⟶ L) [Mono i] [Mono j]
    (hi : Localization.localEquivalences S i)
    (sq : Functor.PushoutObjObj (curriedDiagramTensor C) i j) :
    Localization.localEquivalences S sq.ι := by
  intro W hW
  letI := hW.1
  exact diagramPushoutProduct_local C i j W sq (hi W hW)

/-- SM7 for any model on simplicial-set diagrams with injective cofibrations
and the exact local weak-equivalence class. -/
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
    (sq : Functor.PushoutObjObj (curriedDiagramTensor C) i j) :
    N.categoryWithCofibrations.cofibrations sq.ι ∧
      ((N.categoryWithWeakEquivalences.weakEquivalences i ∨
          HomotopicalAlgebra.weakEquivalences SSet.{u} j) →
        N.categoryWithWeakEquivalences.weakEquivalences sq.ι) := by
  letI : ModelCategory (C ⥤ SSet.{u}) := modelCategory C
  have hbi : (modelCategory C).categoryWithCofibrations.cofibrations i := by
    rw [← hcof]
    exact hi
  haveI : Mono i := by
    have he : (modelCategory C).categoryWithCofibrations.cofibrations =
        monomorphisms (C ⥤ SSet.{u}) := model_cofibrations C
    rw [he] at hbi
    exact hbi
  haveI : Mono j :=
    (SSet.modelCategoryQuillen.cofibration_iff j).mp
      ((HomotopicalAlgebra.cofibration_iff j).mpr hj)
  refine ⟨?_, ?_⟩
  · rw [hcof]
    exact model_pushoutProduct_cofibration C i j hbi hj sq
  · rintro (hwi | hwj)
    · rw [hweak] at hwi ⊢
      exact localEquivalences_pushoutProduct C S i j hwi sq
    · rw [hweak]
      have hjtriv : HomotopicalAlgebra.trivialCofibrations SSet.{u} j :=
        ⟨hj, hwj⟩
      have hwbox := (model_pushoutProduct_trivial_right C i j hbi hjtriv sq).2
      exact Localization.weakEquivalences_le_localEquivalences S sq.ι hwbox

/-- SM7 for the actual injective localization at a small family of
monomorphisms. -/
theorem localized_pushoutProduct_sm7
    (I : Type u) (s : I → Arrow (C ⥤ SSet.{u}))
    (hs : ∀ k, Mono (s k).hom)
    {A B : C ⥤ SSet.{u}} (i : A ⟶ B)
    {K L : SSet.{u}} (j : K ⟶ L)
    (hi : (localizedModelCategory C I s hs).categoryWithCofibrations.cofibrations i)
    (hj : HomotopicalAlgebra.cofibrations SSet.{u} j)
    (sq : Functor.PushoutObjObj (curriedDiagramTensor C) i j) :
    (localizedModelCategory C I s hs).categoryWithCofibrations.cofibrations sq.ι ∧
      (((localizedModelCategory C I s hs).categoryWithWeakEquivalences.weakEquivalences i ∨
          HomotopicalAlgebra.weakEquivalences SSet.{u} j) →
        (localizedModelCategory C I s hs).categoryWithWeakEquivalences.weakEquivalences sq.ι) := by
  have he := localized_exactClasses C I s hs
  exact localizedModel_pushoutProduct_sm7 C
    (diagramLocalizingFamily C I s) (localizedModelCategory C I s hs)
    he.1 he.2 i j hi hj sq

end
end DaggerModels.PartII.InjectiveKanDiagram
