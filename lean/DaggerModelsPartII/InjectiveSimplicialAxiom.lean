import DaggerModelsPartII.DiagramPushoutProduct

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory MorphismProperty HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerModels.PartII.InjectiveKanDiagram
variable (C : Type u) [Category.{u} C]
noncomputable section

local instance : ModelCategory (C ⥤ SSet.{u}) := modelCategory C

/-- The actual injective-model pushout-product is a cofibration when both
inputs are cofibrations. -/
theorem model_pushoutProduct_cofibration {A B : C ⥤ SSet.{u}} (i : A ⟶ B)
    {K L : SSet.{u}} (j : K ⟶ L)
    (hi : HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}) i)
    (hj : HomotopicalAlgebra.cofibrations SSet.{u} j)
    (sq : Functor.PushoutObjObj (curriedDiagramTensor C) i j) :
    HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}) sq.ι := by
  rw [model_cofibrations C] at hi ⊢
  haveI : Mono i := hi
  haveI : Mono j := (SSet.modelCategoryQuillen.cofibration_iff j).mp
    ((HomotopicalAlgebra.cofibration_iff j).mpr hj)
  exact diagramPushoutProduct_mono C i j sq

/-- The pushout-product is a trivial injective cofibration when the diagram
input is a trivial cofibration. -/
theorem model_pushoutProduct_trivial_left {A B : C ⥤ SSet.{u}} (i : A ⟶ B)
    {K L : SSet.{u}} (j : K ⟶ L)
    (hi : HomotopicalAlgebra.trivialCofibrations (C ⥤ SSet.{u}) i)
    (hj : HomotopicalAlgebra.cofibrations SSet.{u} j)
    (sq : Functor.PushoutObjObj (curriedDiagramTensor C) i j) :
    HomotopicalAlgebra.trivialCofibrations (C ⥤ SSet.{u}) sq.ι := by
  haveI : Mono j := (SSet.modelCategoryQuillen.cofibration_iff j).mp
    ((HomotopicalAlgebra.cofibration_iff j).mpr hj)
  have hit : trivialCofibrations C i := by
    change HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}) i ∧
      HomotopicalAlgebra.weakEquivalences (C ⥤ SSet.{u}) i at hi
    rw [model_cofibrations C, model_weakEquivalences C] at hi
    exact hi
  have ht := diagramPushoutProduct_trivial_left C i j hit sq
  change HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}) sq.ι ∧
    HomotopicalAlgebra.weakEquivalences (C ⥤ SSet.{u}) sq.ι
  rw [model_cofibrations C, model_weakEquivalences C]
  exact ht

/-- The pushout-product is a trivial injective cofibration when the simplicial
input is a trivial cofibration. -/
theorem model_pushoutProduct_trivial_right {A B : C ⥤ SSet.{u}} (i : A ⟶ B)
    {K L : SSet.{u}} (j : K ⟶ L)
    (hi : HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}) i)
    (hj : HomotopicalAlgebra.trivialCofibrations SSet.{u} j)
    (sq : Functor.PushoutObjObj (curriedDiagramTensor C) i j) :
    HomotopicalAlgebra.trivialCofibrations (C ⥤ SSet.{u}) sq.ι := by
  haveI : Mono i := by
    rw [model_cofibrations C] at hi
    exact hi
  have ht := diagramPushoutProduct_trivial_right C i j hj sq
  change HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}) sq.ι ∧
    HomotopicalAlgebra.weakEquivalences (C ⥤ SSet.{u}) sq.ι
  rw [model_cofibrations C, model_weakEquivalences C]
  exact ht


/-- Pushout-product SM7 for the actual injective Kan model: two cofibrations
give a cofibration, which is trivial if either input is weakly equivalent. -/
theorem model_pushoutProduct_sm7 {A B : C ⥤ SSet.{u}} (i : A ⟶ B)
    {K L : SSet.{u}} (j : K ⟶ L)
    (hi : HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}) i)
    (hj : HomotopicalAlgebra.cofibrations SSet.{u} j)
    (sq : Functor.PushoutObjObj (curriedDiagramTensor C) i j) :
    HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}) sq.ι ∧
      ((HomotopicalAlgebra.weakEquivalences (C ⥤ SSet.{u}) i ∨
          HomotopicalAlgebra.weakEquivalences SSet.{u} j) →
        HomotopicalAlgebra.weakEquivalences (C ⥤ SSet.{u}) sq.ι) := by
  refine ⟨model_pushoutProduct_cofibration C i j hi hj sq, ?_⟩
  rintro (hwi | hwj)
  · have hit : HomotopicalAlgebra.trivialCofibrations (C ⥤ SSet.{u}) i := by
      change HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}) i ∧
        HomotopicalAlgebra.weakEquivalences (C ⥤ SSet.{u}) i
      exact ⟨hi, hwi⟩
    exact (model_pushoutProduct_trivial_left C i j hit hj sq).2
  · have hjt : HomotopicalAlgebra.trivialCofibrations SSet.{u} j := by
      change HomotopicalAlgebra.cofibrations SSet.{u} j ∧
        HomotopicalAlgebra.weakEquivalences SSet.{u} j
      exact ⟨hj, hwj⟩
    exact (model_pushoutProduct_trivial_right C i j hi hjt sq).2

end
end DaggerModels.PartII.InjectiveKanDiagram
