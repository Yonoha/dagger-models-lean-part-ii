import DaggerModelsPartII.LocalizedQuillenAdjunction

set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
universe v u
namespace DaggerModels.PartII.Localization
noncomputable section

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]
  [HasLimitsOfSize.{0, 0} D] [HasColimitsOfSize.{0, 0} D]
  (MC : ModelCategory C) (MD : ModelCategory D)
  (S : MorphismProperty C) (T : MorphismProperty D)
  (NC : ModelCategory C) (ND : ModelCategory D)
  (hcC : NC.categoryWithCofibrations.cofibrations =
    MC.categoryWithCofibrations.cofibrations)
  (hwC : NC.categoryWithWeakEquivalences.weakEquivalences =
    @localEquivalences C _ MC _ _ S)
  (hcD : ND.categoryWithCofibrations.cofibrations =
    MD.categoryWithCofibrations.cofibrations)
  (hwD : ND.categoryWithWeakEquivalences.weakEquivalences =
    @localEquivalences D _ MD _ _ T)

include hcC hwC in
theorem localizedFibrations_le_baseFibrations :
    NC.categoryWithFibrations.fibrations ≤ MC.categoryWithFibrations.fibrations := by
  have hM : (MC.categoryWithCofibrations.cofibrations ⊓
      MC.categoryWithWeakEquivalences.weakEquivalences).rlp =
        MC.categoryWithFibrations.fibrations := by
    letI := MC
    exact rlp_eq_of_wfs (trivialCofibrations C) (fibrations C)
  have hN : (MC.categoryWithCofibrations.cofibrations ⊓
      @localEquivalences C _ MC _ _ S).rlp = NC.categoryWithFibrations.fibrations := by
    letI := NC
    rw [← hcC, ← hwC]
    exact rlp_eq_of_wfs (trivialCofibrations C) (fibrations C)
  rw [← hM, ← hN]
  apply antitone_rlp
  exact inf_le_inf_left _ (@weakEquivalences_le_localEquivalences C _ MC _ _ S)

include hcC hwC hcD hwD in
/-- An adjunction between base model categories descends to their exact left
localizations when its right adjoint sends local objects to local objects. -/
theorem localizedQuillen_of_rightLocal
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    (hbase : @Adjunction.IsQuillenAdjunction C D _ _ MC MD F G adj)
    (hlocal : ∀ (X : D), @localObject D _ MD _ _ T X →
      @localObject C _ MC _ _ S (G.obj X)) :
    @Adjunction.IsQuillenAdjunction C D _ _ NC ND F G adj := by
  letI : ModelCategory C := NC
  letI : ModelCategory D := ND
  have htriv : G.PreservesTrivialFibrations := by
    apply (adj.preservesTrivialFibrations_iff_preservesCofibrations).mpr
    apply F.preservesCofibrations_iff.mpr
    intro A B i hi
    letI : ModelCategory C := MC
    letI : ModelCategory D := MD
    have hiMC : MC.categoryWithCofibrations.cofibrations i := by
      rw [← hcC]
      exact hi
    haveI : Cofibration i := (cofibration_iff _).mpr hiMC
    letI : @Adjunction.IsQuillenAdjunction C D _ _ MC MD F G adj := hbase
    have hFi : MD.categoryWithCofibrations.cofibrations (F.map i) :=
      (cofibration_iff _).mp (inferInstance : Cofibration (F.map i))
    change ND.categoryWithCofibrations.cofibrations (F.map i)
    rw [hcD]
    exact hFi
  have hfib : ∀ ⦃X Y : D⦄ (p : X ⟶ Y),
      @IsFibrant D _ ND.categoryWithFibrations _ X →
      @IsFibrant D _ ND.categoryWithFibrations _ Y →
      ND.categoryWithFibrations.fibrations p →
      NC.categoryWithFibrations.fibrations (G.map p) := by
    intro X Y p hX hY hp
    have hXloc := localObject_of_localized_fibrant MD T hcD hwD X hX
    have hYloc := localObject_of_localized_fibrant MD T hcD hwD Y hY
    have hpMD : MD.categoryWithFibrations.fibrations p :=
      localizedFibrations_le_baseFibrations MD T ND hcD hwD p hp
    have hpMC : MC.categoryWithFibrations.fibrations (G.map p) := by
      letI : ModelCategory C := MC
      letI : ModelCategory D := MD
      letI : @Adjunction.IsQuillenAdjunction C D _ _ MC MD F G adj := hbase
      haveI : Fibration p := (fibration_iff _).mpr hpMD
      exact (fibration_iff _).mp (inferInstance : Fibration (G.map p))
    exact baseFibration_betweenLocal_isLocalizedFibration MC S hcC hwC
      (G.map p) hpMC (hlocal X hXloc) (hlocal Y hYloc)
  exact quillen_of_trivialFibrations_and_fibrantFibrations F G adj htriv hfib

end
end DaggerModels.PartII.Localization
