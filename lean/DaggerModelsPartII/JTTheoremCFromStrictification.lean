import DaggerModelsPartII.JTFinalAssembly
import DaggerModelsPartII.JTLocalizedFrameComparison
import DaggerModelsPartII.QuillenDerivedUnitOfLocalizedFull
import DaggerModelsPartII.QuillenMateWeakComparison

/-! Assemble the exact Theorem C from the original chosen strictification map. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite DaggerModels

namespace DaggerModels.PartII.TheoremCStatement

open SegalLocalizers ConstantVertexAdjunction
open JTLocalizedFrameComparison QuillenDerivedUnitOfLocalizedFull

noncomputable section

private local instance : HasLimits DaggerSSet.{0} := daggerSSetHasLimits
private local instance : HasColimits DaggerSSet.{0} := daggerSSetHasColimits
private local instance : ModelCategory DaggerSSet.{0} :=
  DaggerActualRigidificationQuillen.modelD.{0}
private local instance : ModelCategory ReverseDaggerSpace.{0} := injectiveSegalModel

private abbrev replacement :=
  InjectiveKanDiagram.localReplacement ReverseSimplexᵒᵖ LocalizerIndex localizerArrow

private def fibrantReplacement : ReverseDaggerSpace.{0} ⥤ FibrantObject ReverseDaggerSpace.{0} :=
  (fibrantObjects ReverseDaggerSpace.{0}).lift replacement fun X ↦
    (InjectiveKanDiagram.localized_isFibrant_iff ReverseSimplexᵒᵖ LocalizerIndex localizerArrow
      localizerArrow_mono _).mpr (InjectiveKanDiagram.localReplacement_isLocal
        ReverseSimplexᵒᵖ LocalizerIndex localizerArrow localizerArrow_mono X)

private def replacementUnit :
    𝟭 ReverseDaggerSpace.{0} ⟶ fibrantReplacement ⋙ FibrantObject.ι :=
  InjectiveKanDiagram.localReplacementUnit ReverseSimplexᵒᵖ LocalizerIndex localizerArrow

private theorem replacementUnit_weak (X : ReverseDaggerSpace.{0}) :
    weakEquivalences ReverseDaggerSpace.{0} (replacementUnit.app X) := by
  change injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences (replacementUnit.app X)
  rw [(InjectiveKanDiagram.localized_exactClasses ReverseSimplexᵒᵖ LocalizerIndex localizerArrow
    localizerArrow_mono).2]
  exact InjectiveKanDiagram.localReplacementUnit_localEquivalence _ _ _ localizerArrow_mono X

/-- Local weakness of the exact chosen strictification gives weakness of the
specified derived unit of the original constant-vertex adjunction. -/
theorem chosenDerivedUnit_weak_of_chosenPsi (hpsi : ChosenPsiWeak) (X : DaggerSSet.{0}) :
    WeakEquivalence (JTChosenUnitTriangle.chosenDerivedUnit X) := by
  letI : adjunction.{0}.IsQuillenAdjunction :=
    JTDeltaFrameNerveTests.isQuillenAdjunction_of_frameNerveTests_detect_weak
      (by
        intro A B f hf
        exact JTFrameNerveDetectionFromStrictification.detect_weak_of_chosenPsi hpsi f hf)
  let hδ : ∀ {A B : DaggerSSet.{0}} (f : A ⟶ B), weakEquivalences DaggerSSet.{0} f →
      weakEquivalences ReverseDaggerSpace.{0} (delta.map f) :=
    fun {_ _} f hf ↦ delta_weak hpsi f hf
  let ff : (localizedLeft hδ).FullyFaithful := localizedDelta_fullyFaithful hpsi
  letI := ff.full
  letI := ff.faithful
  haveI : IsIso ((weakEquivalences DaggerSSet.{0}).Q.map
      (JTChosenUnitTriangle.chosenDerivedUnit X)) := by
    unfold JTChosenUnitTriangle.chosenDerivedUnit
    exact localization_inverts_chosenDerivedUnit adjunction hδ
      fibrantReplacement replacementUnit replacementUnit_weak X
  exact (weakEquivalence_iff _).mpr (QuillenMateWeakComparison.weak_of_localization_isIso
    (weakEquivalences DaggerSSet.{0}).Q (JTChosenUnitTriangle.chosenDerivedUnit X))

/-- The unchanged main equivalence follows from the literal strictification input. -/
theorem mainStatement_of_chosenPsi (hpsi : ChosenPsiWeak) : mainStatement :=
  mainStatement_of_chosenPsi_and_unit hpsi (fun X _ ↦ chosenDerivedUnit_weak_of_chosenPsi hpsi X)

/-- The unchanged four-link assertion follows from the literal strictification input. -/
theorem statement_of_chosenPsi (hpsi : ChosenPsiWeak) : statement :=
  statement_of_mainStatement (mainStatement_of_chosenPsi hpsi)

end

end DaggerModels.PartII.TheoremCStatement
