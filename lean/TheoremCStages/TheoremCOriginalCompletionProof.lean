import OrdinarySegalCSSWeakOrderedRecognition
import RawOrdinaryJTTargetCSSFibrant
import RawOrdinaryJTUnitCSSWeak
import RawOrdinaryJTChosenMapCalibration
import OrdinaryJTOrdinaryInputSegal
import OrdinaryJTOrdinaryInputReedy
import TheoremCFromOriginalRawOrderedUnit

/-!
# The original raw ordered unit and the unchanged four-link Theorem C

Apply ordinary ordered recognition to the literal original curried raw map.
The source is only known injectively fibrant and Segal after forgetting the
reversal structure. The actual raw target is CSS fibrant. Exact endpoint
calibration returns the result to rawChosenFiberMapAtP, and the existing
original raw-unit interface gives all four original Quillen equivalences.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.TheoremCOriginalCompletionProof

open OrdinaryCSSLocalization (Space)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private local instance : ModelCategory Source :=
  InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- The literal original raw chosen map is weak at the specified original
projective-image vertices, with the original source hypothesis unchanged. -/
theorem rawChosenFiberMapAtP_weak (W : Source)
    (hW : Localization.localObject SegalLocalizers.localizingFamily W)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    WeakEquivalence (JTRawOrdinaryAdjoint.rawChosenFiberMapAtP W x y) := by
  have hStrict := (SegalLocalizers.injectiveLocalObject_iff_strict W).mp hW
  haveI : IsFibrant (RawOrdinaryJTQuillenTranspose.input W) :=
    OrdinaryJTOrdinaryInputReedy.ordinaryInput_injectiveFibrant W hStrict.1
  apply (RawOrdinaryJTChosenMapCalibration.rawChosenFiberMapAtP_weak_iff W x y).mpr
  exact OrdinarySegalCSSWeakOrderedRecognition.cssWeak_chosenMappingMap_weak
    (W := RawOrdinaryJTQuillenTranspose.input W)
    (JTRealizationDiagonal.ordinaryCurry.map (JTRawOrdinaryAdjoint.gRawTilde W))
    (OrdinaryJTOrdinaryInputSegal.ordinaryInput_segalCondition W hStrict.2.1)
    (RawOrdinaryJTTargetCSSFibrant.rawTarget_cssFibrant W)
    (RawOrdinaryJTUnitCSSWeak.rawTranspose_cssWeak W) _ _

/-- The exact original raw ordered-unit premise is now discharged. -/
theorem originalRawOrderedUnitWeak :
    JTTheoremCFromOriginalRawOrderedUnit.OriginalRawOrderedUnitWeak := by
  intro W hW x y
  exact rawChosenFiberMapAtP_weak W hW x y

/-- All four original Quillen equivalences, with the actual original models,
adjoints, and left-adjoint directions in the unchanged Theorem C statement. -/
theorem original_statement : TheoremCStatement.statement :=
  JTTheoremCFromOriginalRawOrderedUnit.statement_of_originalRawOrderedUnit
    originalRawOrderedUnitWeak

#print axioms rawChosenFiberMapAtP_weak
#print axioms originalRawOrderedUnitWeak
#print axioms original_statement

end

end DaggerModels.PartII.TheoremCOriginalCompletionProof
