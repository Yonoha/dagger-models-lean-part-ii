import OrdinarySpaceReedyMono
import OrdinaryJTReedyQuillen
import DaggerModelsPartII.InjectiveKanModel
import DaggerModelsPartII.MappingCofibrationInclusion

/-!
# The exact ordinary Reedy and injective Kan diagram classes

The all-monomorphisms direction uses the actual relative latching theorem.
For the converse, the existing `ReedyProperties.reedyCofibration_eval`
argument works with Kan coefficients: latching functors preserve the
left lifting property, and pushouts preserve cofibrations. The two models
then have identical weak classes and hence identical fibrations by the
existing `fibrations_le_of_cofibrations_le` theorem.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySpaceReedyInjective

noncomputable section

abbrev Space := SimplexCategoryᵒᵖ ⥤ SSet.{0}

/-- The checked Kan Reedy model. -/
def reedyModel : ModelCategory Space := OrdinaryJTReedyQuillen.diagramModel

/-- The existing injective Kan diagram model used by ordinary CSS localization. -/
def injectiveModel : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private theorem reedyCofibration_eval {W V : Space} (f : W ⟶ V)
    (hf : reedyLatchingProperty (cofibrations SSet.{0}) f) (n : ℕ) :
    cofibrations SSet.{0} (f.app (op ⦋n⦌)) := by
  let P := cofibrations SSet.{0}
  have hm : P ((latchingFunctor n).map f) := by
    change cofibrations SSet.{0} ((latchingFunctor n).map f)
    rw [← llp_eq_of_wfs (cofibrations SSet.{0}) (trivialFibrations SSet.{0})]
    apply latchingFunctor_map_llp
    intro m _
    rw [llp_eq_of_wfs (cofibrations SSet.{0}) (trivialFibrations SSet.{0})]
    exact hf m
  rw [← inl_comp_relativeLatchingMap f n]
  exact P.comp_mem _ _ (P.pushout_inl _ _ hm) (hf n)

/-- The actual Reedy cofibrations of ordinary simplicial spaces are all monomorphisms. -/
theorem reedy_cofibrations_eq_monomorphisms :
    reedyModel.categoryWithCofibrations.cofibrations = monomorphisms Space := by
  ext W V f
  constructor
  · intro hf
    change reedyLatchingProperty (cofibrations SSet.{0}) f at hf
    apply (NatTrans.mono_iff_mono_app f).mpr
    intro m
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, op ⦋n⦌ = m :=
      ⟨m.unop.len, congrArg op (SimplexCategory.ext _ _ rfl)⟩
    have h := reedyCofibration_eval f hf n
    rw [SSet.modelCategoryQuillen.cofibrations_eq] at h
    exact h
  · intro hf
    change Mono f at hf
    letI : Mono f := hf
    exact OrdinarySpaceReedyMono.mono_reedyCofibration f

/-- The two original models have identical cofibration classes. -/
theorem cofibrations_eq :
    reedyModel.categoryWithCofibrations.cofibrations =
      injectiveModel.categoryWithCofibrations.cofibrations :=
  reedy_cofibrations_eq_monomorphisms.trans
    (InjectiveKanDiagram.model_cofibrations SimplexCategoryᵒᵖ).symm

/-- Both models use precisely levelwise native Kan weak equivalences. -/
theorem weakEquivalences_eq :
    reedyModel.categoryWithWeakEquivalences.weakEquivalences =
      injectiveModel.categoryWithWeakEquivalences.weakEquivalences :=
  (InjectiveKanDiagram.model_weakEquivalences SimplexCategoryᵒᵖ).symm

/-- The actual relative-matching and injective fibration classes coincide. -/
theorem fibrations_eq :
    reedyModel.categoryWithFibrations.fibrations =
      injectiveModel.categoryWithFibrations.fibrations := by
  apply le_antisymm
  · exact fibrations_le_of_cofibrations_le injectiveModel reedyModel
      cofibrations_eq.symm.le weakEquivalences_eq.symm
  · exact fibrations_le_of_cofibrations_le reedyModel injectiveModel
      cofibrations_eq.le weakEquivalences_eq

/-- The original ordinary JT right adjoint preserves injective Kan fibrations. -/
theorem right_map_fibration {X Y : SSet.{0}} (p : X ⟶ Y)
    (hp : OrdinaryJTProjectiveQuillen.joyalModel.categoryWithFibrations.fibrations p) :
    injectiveModel.categoryWithFibrations.fibrations
      (OrdinaryJTCurriedAdjunction.right.map p) := by
  rw [← fibrations_eq]
  exact OrdinaryJTReedyQuillen.right_map_fibration p hp

/-- The actual ordinary JT adjunction is Quillen also for the injective
Kan base model used by the ordinary CSS localization. -/
theorem isQuillenAdjunction :
    @Adjunction.IsQuillenAdjunction Space SSet.{0} _ _ injectiveModel
      OrdinaryJTProjectiveQuillen.joyalModel
      OrdinaryJTCurriedAdjunction.left OrdinaryJTCurriedAdjunction.right
      OrdinaryJTCurriedAdjunction.adjunction := by
  let M := OrdinaryJTProjectiveQuillen.joyalModel
  let L := OrdinaryJTCurriedAdjunction.left
  let R := OrdinaryJTCurriedAdjunction.right
  let a := OrdinaryJTCurriedAdjunction.adjunction
  letI : ModelCategory Space := injectiveModel
  letI : ModelCategory SSet.{0} := M
  letI : CategoryWithFibrations SSet.{0} := M.categoryWithFibrations
  letI : CategoryWithCofibrations SSet.{0} := M.categoryWithCofibrations
  letI : CategoryWithWeakEquivalences SSet.{0} := M.categoryWithWeakEquivalences
  letI : R.PreservesFibrations := R.preservesFibrations_iff.mpr
    (fun _ _ p hp ↦ right_map_fibration p hp)
  have htriv : R.PreservesTrivialFibrations := by
    constructor
    intro X Y p hp
    have h := OrdinaryJTReedyQuillen.right_map_trivialFibration p hp.1 hp.2
    change injectiveModel.categoryWithFibrations.fibrations (R.map p) ∧
      injectiveModel.categoryWithWeakEquivalences.weakEquivalences (R.map p)
    rw [← fibrations_eq, ← weakEquivalences_eq]
    exact h
  letI : L.PreservesCofibrations :=
    a.preservesTrivialFibrations_iff_preservesCofibrations.mp htriv
  exact ⟨⟩

#print axioms reedy_cofibrations_eq_monomorphisms
#print axioms cofibrations_eq
#print axioms weakEquivalences_eq
#print axioms fibrations_eq
#print axioms right_map_fibration
#print axioms isQuillenAdjunction

end

end DaggerModels.PartII.OrdinarySpaceReedyInjective
