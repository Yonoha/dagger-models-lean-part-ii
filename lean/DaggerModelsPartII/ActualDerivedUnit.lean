import DaggerModelsPartII.CofibrantUnit
import DaggerModelsPartII.RestrictionInjectiveQuillen

/-!
# The actual derived change-of-index unit

Choose an objectwise fibrant replacement in the actual localized projective
model by factoring the map to the terminal object. The original adjunction
unit followed by its restriction is a local weak equivalence on projectively
cofibrant reversal diagrams.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MorphismProperty DaggerModels

namespace DaggerModels.PartII.ActualDerivedUnit

open SegalLocalizers ActualIndexProjectiveModel CofibrantUnit

noncomputable section

private local instance : ModelCategory ActualSpace := actualSegalModel

/-- A chosen objectwise fibrant replacement in the actual localized projective model. -/
private def replacementData (X : ReverseDaggerSpace.{0}) :=
  MorphismProperty.factorizationData (trivialCofibrations ActualSpace)
    (fibrations ActualSpace) (terminal.from ((actualLeftExtension.{0}).obj X))

def fibrantReplacementObject (X : ReverseDaggerSpace.{0}) : ActualSpace :=
  (replacementData X).Z

def fibrantReplacementMap (X : ReverseDaggerSpace.{0}) :
    (actualLeftExtension.{0}).obj X ⟶ fibrantReplacementObject X :=
  (replacementData X).i

theorem fibrantReplacementMap_weak (X : ReverseDaggerSpace.{0}) :
    actualSegalModel.categoryWithWeakEquivalences.weakEquivalences
      (fibrantReplacementMap X) :=
  (replacementData X).hi.2

theorem fibrantReplacementObject_fibrant (X : ReverseDaggerSpace.{0}) :
    @IsFibrant ActualSpace _ actualSegalModel.categoryWithFibrations _
      (fibrantReplacementObject X) := by
  letI : ModelCategory ActualSpace := actualSegalModel
  exact (isFibrant_iff_of_isTerminal (replacementData X).p terminalIsTerminal).mpr
    ((fibration_iff _).mpr (replacementData X).hp)

def derivedUnitMap (X : ReverseDaggerSpace.{0}) :
    X ⟶ (actualRestriction.{0}).obj (fibrantReplacementObject X) :=
  (actualLeftAdjunction.{0}).unit.app X ≫
    (actualRestriction.{0}).map (fibrantReplacementMap X)

private theorem reversal_models_weakEquivalences_eq :
    projectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences =
      injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences := by
  have hp := ProjectiveKanDiagram.localized_exactClasses ReverseSimplexᵒᵖ
    LocalizerIndex localizerArrow localizerArrow_mono
  have hi := InjectiveKanDiagram.localized_exactClasses ReverseSimplexᵒᵖ
    LocalizerIndex localizerArrow localizerArrow_mono
  exact hp.2.trans
    ((ProjectiveInjectiveComparison.localEquivalences_eq _ _).trans hi.2.symm)

/-- The chosen derived unit is a local weak equivalence for every object
cofibrant in the localized projective reversal model. -/
theorem derivedUnitMap_weak_of_localizedProjectiveCofibrant
    (X : ReverseDaggerSpace.{0})
    (hX : @IsCofibrant ReverseDaggerSpace.{0} _
      projectiveSegalModel.categoryWithCofibrations _ X) :
    projectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
      (derivedUnitMap X) := by
  have hq : actualInjectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
      (fibrantReplacementMap X) := by
    rw [← actualSegalModels_weakEquivalences_eq]
    exact fibrantReplacementMap_weak X
  have hr := RestrictionInjectiveQuillen.actualRestriction_preservesLocalizedInjectiveWeak
    (fibrantReplacementMap X) hq
  have hη := (actualUnit_trivial_of_localizedProjectiveCofibrant X hX).2
  rw [reversal_models_weakEquivalences_eq]
  exact injectiveSegalModel.cm2.comp_mem _ _ hη hr

/-- The manuscript's projectively cofibrant input has the same derived-unit conclusion. -/
theorem derivedUnitMap_weak_of_projectiveCofibrant
    (X : ReverseDaggerSpace.{0})
    (hX : @IsCofibrant ReverseDaggerSpace.{0} _
      (ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ).categoryWithCofibrations _ X) :
    projectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
      (derivedUnitMap X) := by
  have hbase : (ProjectiveKanDiagram.modelCategory
      ReverseSimplexᵒᵖ).categoryWithCofibrations.cofibrations (initial.to X) := by
    letI : CategoryWithCofibrations ReverseDaggerSpace.{0} :=
      (ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ).categoryWithCofibrations
    exact (cofibration_iff (initial.to X)).mp hX
  have hloc : projectiveSegalModel.categoryWithCofibrations.cofibrations (initial.to X) := by
    change (ProjectiveKanDiagram.localizedModelCategory ReverseSimplexᵒᵖ
      LocalizerIndex localizerArrow localizerArrow_mono).categoryWithCofibrations.cofibrations
        (initial.to X)
    rw [(ProjectiveKanDiagram.localized_exactClasses ReverseSimplexᵒᵖ
      LocalizerIndex localizerArrow localizerArrow_mono).1]
    exact hbase
  have hXloc : @IsCofibrant ReverseDaggerSpace.{0} _
      projectiveSegalModel.categoryWithCofibrations _ X := by
    letI : CategoryWithCofibrations ReverseDaggerSpace.{0} :=
      projectiveSegalModel.categoryWithCofibrations
    exact (cofibration_iff (initial.to X)).mpr hloc
  exact derivedUnitMap_weak_of_localizedProjectiveCofibrant X hXloc

end

end DaggerModels.PartII.ActualDerivedUnit
