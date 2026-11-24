import DaggerModelsPartII.LocalizedQuillenDescent

/-!
# Quillen descent through a source localization

An adjunction that is Quillen for base model categories remains Quillen when
only its source is left localized, provided the right adjoint sends fibrant
target objects to local source objects. The target model category is unchanged.
-/

set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

universe v u
namespace DaggerModels.PartII.Localization
noncomputable section

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]
  [HasLimitsOfSize.{0, 0} D]
  (MC : ModelCategory C) (MD : ModelCategory D)
  (S : MorphismProperty C)
  (NC : ModelCategory C)
  (hcC : NC.categoryWithCofibrations.cofibrations =
    MC.categoryWithCofibrations.cofibrations)
  (hwC : NC.categoryWithWeakEquivalences.weakEquivalences =
    @localEquivalences C _ MC _ _ S)

include hcC hwC in
/-- An adjunction to an unchanged target model category descends through an exact
left localization of its source when its right adjoint sends fibrant target
objects to local source objects. -/
theorem leftLocalizedQuillen_of_rightFibrantLocal
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    (baseQuillen : @Adjunction.IsQuillenAdjunction C D _ _ MC MD F G adj)
    (hlocal : ∀ (X : D), @IsFibrant D _ MD.categoryWithFibrations _ X →
      @localObject C _ MC _ _ S (G.obj X)) :
    @Adjunction.IsQuillenAdjunction C D _ _ NC MD F G adj := by
  letI : ModelCategory C := NC
  letI : ModelCategory D := MD
  have htriv : G.PreservesTrivialFibrations := by
    apply (adj.preservesTrivialFibrations_iff_preservesCofibrations).mpr
    apply F.preservesCofibrations_iff.mpr
    intro A B i hi
    letI : ModelCategory C := MC
    have hiMC : MC.categoryWithCofibrations.cofibrations i := by
      rw [← hcC]
      exact hi
    haveI : Cofibration i := (cofibration_iff _).mpr hiMC
    letI : @Adjunction.IsQuillenAdjunction C D _ _ MC MD F G adj := baseQuillen
    exact (cofibration_iff _).mp (inferInstance : Cofibration (F.map i))
  have hfib : ∀ ⦃X Y : D⦄ (p : X ⟶ Y),
      @IsFibrant D _ MD.categoryWithFibrations _ X →
      @IsFibrant D _ MD.categoryWithFibrations _ Y →
      MD.categoryWithFibrations.fibrations p →
      NC.categoryWithFibrations.fibrations (G.map p) := by
    intro X Y p hX hY hp
    have hpMC : MC.categoryWithFibrations.fibrations (G.map p) := by
      letI : ModelCategory C := MC
      haveI : Fibration p := (fibration_iff _).mpr hp
      letI : @Adjunction.IsQuillenAdjunction C D _ _ MC MD F G adj := baseQuillen
      exact (fibration_iff _).mp (inferInstance : Fibration (G.map p))
    exact baseFibration_betweenLocal_isLocalizedFibration MC S hcC hwC
      (G.map p) hpMC (hlocal X hX) (hlocal Y hY)
  exact quillen_of_trivialFibrations_and_fibrantFibrations F G adj htriv hfib

end
end DaggerModels.PartII.Localization
