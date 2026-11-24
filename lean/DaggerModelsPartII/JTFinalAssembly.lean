import DaggerModelsPartII.ActualLocalizedEquivalence
import DaggerModelsPartII.ConstantVertexReflection
import DaggerModelsPartII.JTChosenUnitTriangle
import DaggerModelsPartII.JTFrameNerveDetectionFromStrictification

/-! Assemble the literal Theorem C and its zigzag from the remaining strictification
and derived-unit weak-equivalence inputs. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite DaggerModels

namespace DaggerModels.PartII.TheoremCStatement

open SegalLocalizers ConstantVertexAdjunction JTStrictificationCoefficients

private local instance : HasLimits DaggerSSet.{0} := daggerSSetHasLimits
private local instance : HasColimits DaggerSSet.{0} := daggerSSetHasColimits
private noncomputable local instance : ModelCategory DaggerSSet.{0} :=
  DaggerOriginalJoyalModel.standardModelCategory.{0}
private noncomputable local instance : ModelCategory ReverseDaggerSpace.{0} := injectiveSegalModel

/-- Local weakness of the chosen strictification and weakness of the chosen derived unit
give the Quillen equivalence of the original constant-vertex adjunction. -/
theorem mainStatement_of_chosenPsi_and_unit
    (hpsi : ∀ Z, (letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
        Localization.localObject localizingFamily Z) →
      weakEquivalences ReverseDaggerSpace.{0} (chosenPsi Z))
    (hunit : ∀ (X : DaggerSSet.{0}) [IsCofibrant X],
      WeakEquivalence (JTChosenUnitTriangle.chosenDerivedUnit X)) :
    mainStatement := by
  letI : adjunction.{0}.IsQuillenAdjunction :=
    JTDeltaFrameNerveTests.isQuillenAdjunction_of_frameNerveTests_detect_weak
      (by
        intro A B f hf
        exact JTFrameNerveDetectionFromStrictification.detect_weak_of_chosenPsi hpsi f hf)
  exact DerivedUnitQuillenCriterion.isQuillenEquivalence_of_derivedUnit_and_reflection
    delta vertex adjunction inferInstance (fun f hf ↦ (weakEquivalence_iff _).mpr
      (vertex_reflects_weak_between_fibrant f ((weakEquivalence_iff _).mp hf))) hunit

/-- The three previously verified Quillen equivalences assemble with the original
constant-vertex equivalence in their specified directions. -/
theorem statement_of_mainStatement (h : mainStatement) : statement :=
  ⟨DaggerActualDaggerQuillenEquivalenceProof.quillen_verified.{0}, h,
    segalIdentity_isQuillenEquivalence,
    ActualLocalizedEquivalence.actualLeftAdjunction_isQuillenEquivalence⟩

end DaggerModels.PartII.TheoremCStatement
