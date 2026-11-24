import OrdinaryChosenCSSCompletion
import OrdinaryPrecompletionUnitCSSWeak

/-!
# Actual weak extensions through the chosen CSS completion

The original unit and the specified replacement inclusion are monic and CSS
weak. Their composite is an actual CSS trivial cofibration, so the existing
model-category lifting property extends every map into a CSS fibrant target.
Two-of-three makes the same extension CSS weak when the original map is weak.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryCSSCompletionExtension

open OrdinaryCSSLocalization (Space)
open OrdinaryChosenCSSCompletion (completion inclusion unit)

noncomputable section

private abbrev C := OrdinaryCSSLocalization.model
private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- The same actual composite completion unit is a CSS cofibration. -/
theorem unit_cssCofibration (W : Space) :
    C.categoryWithCofibrations.cofibrations (unit W) := by
  haveI : Mono (OrdinarySegalVerticalPrecompletion.unit W) :=
    OrdinaryPrecompletionUnitCSSWeak.unit_mono W
  haveI : Mono (inclusion W) := OrdinaryChosenCSSCompletion.inclusion_mono W
  haveI : Mono (unit W) := by
    change Mono (OrdinarySegalVerticalPrecompletion.unit W ≫ inclusion W)
    infer_instance
  change OrdinaryCSSLocalization.model.categoryWithCofibrations.cofibrations (unit W)
  rw [OrdinaryCSSLocalization.exactClasses.1]
  change cofibrations Space (unit W)
  rw [InjectiveKanDiagram.model_cofibrations]
  exact monomorphisms.infer_property _

/-- The actual composite unit is CSS weak for the original fibrant Segal input. -/
theorem unit_cssWeak (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) :
    C.categoryWithWeakEquivalences.weakEquivalences (unit W) := by
  letI : ModelCategory Space := C
  letI : CategoryWithWeakEquivalences Space := C.categoryWithWeakEquivalences
  haveI : WeakEquivalence (OrdinarySegalVerticalPrecompletion.unit W) :=
    (weakEquivalence_iff _).mpr (OrdinaryPrecompletionUnitCSSWeak.unit_cssWeak W hSegal)
  haveI : WeakEquivalence (inclusion W) :=
    (weakEquivalence_iff _).mpr (OrdinaryChosenCSSCompletion.inclusion_cssWeak W)
  change weakEquivalences Space
    (OrdinarySegalVerticalPrecompletion.unit W ≫ inclusion W)
  exact mem_weakEquivalences _

/-- Extend the original map across the same actual completion unit. -/
theorem exists_extension {W Z : Space} [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (hZ : @IsFibrant Space _ C.categoryWithFibrations _ Z) (f : W ⟶ Z) :
    ∃ g : completion W ⟶ Z, unit W ≫ g = f := by
  letI : ModelCategory Space := C
  letI : CategoryWithCofibrations Space := C.categoryWithCofibrations
  letI : CategoryWithFibrations Space := C.categoryWithFibrations
  letI : CategoryWithWeakEquivalences Space := C.categoryWithWeakEquivalences
  haveI : IsFibrant Z := hZ
  haveI : Cofibration (unit W) := (cofibration_iff _).mpr (unit_cssCofibration W)
  haveI : WeakEquivalence (unit W) := (weakEquivalence_iff _).mpr (unit_cssWeak W hSegal)
  let sq : CommSq f (unit W) (terminal.from Z) (terminal.from (completion W)) :=
    ⟨terminalIsTerminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- A CSS weak original map has a CSS weak extension through that same unit. -/
theorem exists_weak_extension {W Z : Space} [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W)
    (hZ : @IsFibrant Space _ C.categoryWithFibrations _ Z) (f : W ⟶ Z)
    (hf : C.categoryWithWeakEquivalences.weakEquivalences f) :
    ∃ g : completion W ⟶ Z, unit W ≫ g = f ∧
      C.categoryWithWeakEquivalences.weakEquivalences g := by
  obtain ⟨g, hg⟩ := exists_extension hSegal hZ f
  refine ⟨g, hg, ?_⟩
  letI : ModelCategory Space := C
  letI : CategoryWithWeakEquivalences Space := C.categoryWithWeakEquivalences
  haveI : WeakEquivalence f := (weakEquivalence_iff _).mpr hf
  haveI : WeakEquivalence (unit W) := (weakEquivalence_iff _).mpr (unit_cssWeak W hSegal)
  exact (weakEquivalence_iff _).mp (weakEquivalence_of_precomp_of_fac hg)

#print axioms unit_cssCofibration
#print axioms unit_cssWeak
#print axioms exists_extension
#print axioms exists_weak_extension

end

end DaggerModels.PartII.OrdinaryCSSCompletionExtension
