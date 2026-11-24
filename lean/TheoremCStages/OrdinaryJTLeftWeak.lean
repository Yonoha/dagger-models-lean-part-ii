import OrdinaryJTCSSQuillen
import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma

/-!
# Weak equivalences under the actual ordinary JT realization

Brown's factorization shows that a left Quillen functor preserves weak
equivalences between cofibrant objects. Every object of the exact ordinary
CSS localization is cofibrant, so the actual curried realization preserves
all of its weak equivalences in the original ordinary Joyal model.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits HomotopicalAlgebra

namespace DaggerModels.PartII.OrdinaryJTLeftWeak

noncomputable section

private theorem map_weak_of_cofibrant
    {C D : Type*} [Category* C] [Category* D]
    [ModelCategory C] [ModelCategory D]
    (F : C ⥤ D) [F.PreservesTrivialCofibrations]
    {X Y : C} [IsCofibrant X] [IsCofibrant Y]
    (f : X ⟶ Y) [WeakEquivalence f] : WeakEquivalence (F.map f) := by
  let h : CofibrantBrownFactorization f := Classical.choice inferInstance
  haveI : Cofibration h.i := (cofibration_iff _).mpr h.hi
  haveI : Cofibration h.s := h.cofibration_s
  haveI : WeakEquivalence h.i := inferInstance
  haveI : WeakEquivalence h.s := inferInstance
  haveI : WeakEquivalence (F.map h.i) := inferInstance
  haveI : WeakEquivalence (F.map h.s) := inferInstance
  have hsp : F.map h.s ≫ F.map h.p = 𝟙 (F.obj Y) := by
    rw [← F.map_comp, h.s_p, F.map_id]
  haveI : WeakEquivalence (F.map h.p) :=
    weakEquivalence_of_precomp_of_fac hsp
  rw [← h.fac, F.map_comp]
  infer_instance

private theorem css_isCofibrant
    (X : OrdinaryCSSLocalization.Space) :
    @IsCofibrant OrdinaryCSSLocalization.Space _
      OrdinaryCSSLocalization.model.categoryWithCofibrations _ X := by
  letI : ModelCategory OrdinaryCSSLocalization.Space := OrdinaryCSSLocalization.model
  letI : CategoryWithCofibrations OrdinaryCSSLocalization.Space :=
    OrdinaryCSSLocalization.model.categoryWithCofibrations
  rw [isCofibrant_iff, cofibration_iff]
  change OrdinaryCSSLocalization.model.categoryWithCofibrations.cofibrations
    (initial.to X)
  rw [OrdinaryCSSLocalization.exactClasses.1]
  letI : ModelCategory OrdinaryCSSLocalization.Space :=
    InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ
  letI : CategoryWithCofibrations OrdinaryCSSLocalization.Space :=
    (InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ).categoryWithCofibrations
  exact (cofibration_iff _).mp
    (InjectiveKanDiagram.model_isCofibrant SimplexCategoryᵒᵖ X)

/-- The actual curried ordinary JT realization sends every weak equivalence
of the exact ordinary CSS model to an original ordinary Joyal weak equivalence. -/
theorem left_map_weak {X Y : OrdinaryCSSLocalization.Space} (f : X ⟶ Y)
    (hf : OrdinaryCSSLocalization.model.categoryWithWeakEquivalences.weakEquivalences f) :
    OrdinaryJTProjectiveQuillen.joyalModel.categoryWithWeakEquivalences.weakEquivalences
      (OrdinaryJTCurriedAdjunction.left.map f) := by
  letI : ModelCategory OrdinaryCSSLocalization.Space := OrdinaryCSSLocalization.model
  letI : CategoryWithCofibrations OrdinaryCSSLocalization.Space :=
    OrdinaryCSSLocalization.model.categoryWithCofibrations
  letI : CategoryWithFibrations OrdinaryCSSLocalization.Space :=
    OrdinaryCSSLocalization.model.categoryWithFibrations
  letI : CategoryWithWeakEquivalences OrdinaryCSSLocalization.Space :=
    OrdinaryCSSLocalization.model.categoryWithWeakEquivalences
  letI : ModelCategory SSet.{0} := OrdinaryJTProjectiveQuillen.joyalModel
  letI : CategoryWithCofibrations SSet.{0} :=
    OrdinaryJTProjectiveQuillen.joyalModel.categoryWithCofibrations
  letI : CategoryWithFibrations SSet.{0} :=
    OrdinaryJTProjectiveQuillen.joyalModel.categoryWithFibrations
  letI : CategoryWithWeakEquivalences SSet.{0} :=
    OrdinaryJTProjectiveQuillen.joyalModel.categoryWithWeakEquivalences
  letI : OrdinaryJTCurriedAdjunction.adjunction.IsQuillenAdjunction :=
    OrdinaryJTCSSQuillen.isQuillenAdjunction
  letI : OrdinaryJTCurriedAdjunction.left.PreservesTrivialCofibrations :=
    Adjunction.IsQuillenAdjunction.preservesTrivialCofibrations
      OrdinaryJTCurriedAdjunction.adjunction
  letI : IsCofibrant X := css_isCofibrant X
  letI : IsCofibrant Y := css_isCofibrant Y
  letI : WeakEquivalence f := (weakEquivalence_iff f).mpr hf
  exact (weakEquivalence_iff _).mp
    (map_weak_of_cofibrant OrdinaryJTCurriedAdjunction.left f)

#print axioms left_map_weak

end

end DaggerModels.PartII.OrdinaryJTLeftWeak
