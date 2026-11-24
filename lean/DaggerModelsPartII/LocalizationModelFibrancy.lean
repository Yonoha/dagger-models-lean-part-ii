import DaggerModelsPartII.LocalEquivalenceClasses
import DaggerModelsPartII.MappingChangeModel

/-! Fibrant objects forced by the exact classes of a left localization. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

universe v u

namespace DaggerModels.PartII.Localization

noncomputable section

variable {C : Type u} [Category.{v} C]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]
  [N : ModelCategory C] (M : ModelCategory C) (S : MorphismProperty C)
  (hc : N.categoryWithCofibrations.cofibrations = M.categoryWithCofibrations.cofibrations)
  (hw : N.categoryWithWeakEquivalences.weakEquivalences = @localEquivalences C _ M _ _ S)

include hc hw in
private theorem localized_fibrations_le :
    N.categoryWithFibrations.fibrations ≤ M.categoryWithFibrations.fibrations := by
  letI := N
  have hM : (M.categoryWithCofibrations.cofibrations ⊓
      M.categoryWithWeakEquivalences.weakEquivalences).rlp =
        M.categoryWithFibrations.fibrations := by
    letI := M
    exact rlp_eq_of_wfs (HomotopicalAlgebra.trivialCofibrations C)
      (HomotopicalAlgebra.fibrations C)
  have hN : (M.categoryWithCofibrations.cofibrations ⊓
      @localEquivalences C _ M _ _ S).rlp = N.categoryWithFibrations.fibrations := by
    rw [← hc, ← hw]
    exact rlp_eq_of_wfs (HomotopicalAlgebra.trivialCofibrations C)
      (HomotopicalAlgebra.fibrations C)
  rw [← hM, ← hN]
  apply antitone_rlp
  exact inf_le_inf_left _ (@weakEquivalences_le_localEquivalences C _ M _ _ S)

include hc hw in
/-- Fibrancy for the exact localized classes implies original fibrancy and locality. -/
theorem localObject_of_localized_fibrant (W : C)
    (hW : @IsFibrant C _ N.categoryWithFibrations _ W) :
    @localObject C _ M _ _ S W := by
  letI := N
  have hp : HomotopicalAlgebra.fibrations C (terminal.from W) := by
    letI := hW
    exact mem_fibrations _
  have hb := localized_fibrations_le M S hc hw _ hp
  have hBase : @IsFibrant C _ M.categoryWithFibrations _ W := by
    letI := M
    exact (isFibrant_iff _).mpr ((fibration_iff _).mpr hb)
  refine ⟨hBase, ?_⟩
  intro A B s hs
  apply (homotopyMappingWeakEquivalences_iff_of_cofibrations_eq
    M N hc.symm W hBase hW s).mpr
  letI := hW
  apply weakEquivalences_le_homotopyMappingWeakEquivalences W s
  change N.categoryWithWeakEquivalences.weakEquivalences s
  rw [hw]
  exact @family_le_localEquivalences C _ M _ _ S A B s hs

include hc hw in
/-- A model with the original cofibrations and exact local weak equivalences
has exactly the original fibrant local objects as its fibrant objects. -/
theorem localized_isFibrant_iff (W : C) :
    @IsFibrant C _ N.categoryWithFibrations _ W ↔ @localObject C _ M _ _ S W := by
  letI := N
  refine ⟨localObject_of_localized_fibrant M S hc hw W, ?_⟩
  intro hW
  let d := factorizationData (HomotopicalAlgebra.trivialCofibrations C)
    (HomotopicalAlgebra.fibrations C) (terminal.from W)
  have hY : IsFibrant d.Z := (isFibrant_iff_of_isTerminal d.p terminalIsTerminal).mpr
    ((fibration_iff _).mpr d.hp)
  have hY' := localObject_of_localized_fibrant M S hc hw d.Z hY
  have hd : @localEquivalences C _ M _ _ S _ _ d.i := hw ▸ d.hi.2
  have hweak : M.categoryWithWeakEquivalences.weakEquivalences d.i := by
    letI := M
    exact (localEquivalence_iff_weak_of_local S d.i hW hY').mp hd
  have hcof : M.categoryWithCofibrations.cofibrations d.i := hc ▸ d.hi.1
  have hex : ∃ r : d.Z ⟶ W, d.i ≫ r = 𝟙 W := by
    letI := M
    letI : IsFibrant W := hW.1
    have sq : CommSq (𝟙 W) d.i (terminal.from W) (terminal.from d.Z) :=
      ⟨terminal.hom_ext _ _⟩
    letI := hasLiftingProperty_of_wfs d.i (terminal.from W)
      (show HomotopicalAlgebra.trivialCofibrations C d.i from ⟨hcof, hweak⟩)
      (mem_fibrations _)
    exact ⟨sq.lift, sq.fac_left⟩
  obtain ⟨r, hr⟩ := hex
  let e : RetractArrow (terminal.from W) (terminal.from d.Z) := {
    i := Arrow.homMk d.i (𝟙 _) (terminal.hom_ext _ _)
    r := Arrow.homMk r (𝟙 _) (terminal.hom_ext _ _)
    retract := by ext <;> simp [hr] }
  exact (isFibrant_iff _).mpr ((fibration_iff _).mpr
    ((HomotopicalAlgebra.fibrations C).of_retract e
      ((fibration_iff _).mp ((isFibrant_iff _).mp hY))))

end

end DaggerModels.PartII.Localization
