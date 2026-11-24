import DaggerModelsPartII.JTJointBeadNormalizedParameter
import DaggerModelsPartII.JTSupportedNormalizedEvaluation

/-! Full internal-necklace comparisons for each actually supported joint bead.
These comparisons retain the full old time and do not select a natural global
normalization of a multi-bead interval. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTJointBeadNormalizedEvaluation

open JTParametrizedTargetFamilies (Family evaluate)
open JTProjectiveOrderedFiberComparison (row)
open JTParametrizedBeadGraph (jointCoefficient fullBeadSupportInclusion)
open JTJointBeadSupportedNormalization (SupportedData)
open JTPointTargetEvaluationCone (pointTarget center)
open JTJointBeadNormalizedParameter (supportedPadded originalPadded supportedPadded_fac)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (a : A) (d : ℕ) (j : JTTargetJointMarks.Joint Q.code)
variable (r : (single d).toSSet ⟶
  (JTTargetIntervalPullback.sourceInterval (F.collapse.app a) j j le_rfl).toSSet)
variable (N : SupportedData F a d j r)

private abbrev incl := fullBeadSupportInclusion F a d
  (r ≫ JTTargetIntervalGluing.middleInclusion (F.collapse.app a) j)

/-- The supported constant triple, on the entire original time simplex. -/
abbrev supportedFamily :=
  JTSupportedNormalizedEvaluation.supportedFamily (W := W) (z := jointCoefficient (Q := Q) j)
    (supportedPadded F a d j r)

/-- The full-degree normalized label, with the same old padded-time parameter. -/
abbrev normalizedFamily :=
  JTSupportedNormalizedEvaluation.normalizedFamily N.data (incl F a d j r)
    (N.middle_onSupport F a d j r) N.front_onSupport N.back_onSupport
    (supportedPadded F a d j r)

/-- The normalized Family parameter is exactly the original whole padded one. -/
theorem normalized_parameter (b : Discrete PUnit) :
    (normalizedFamily F a d j r N).parameter b = originalPadded F a d j r :=
  supportedPadded_fac F a d j r

/-- Compare the complete endpoint-reduced internal-necklace presentations. -/
abbrev presentation := JTSupportedNormalizedEvaluation.presentation
  (n := time.obj a) N.data (incl F a d j r)
    (N.middle_onSupport F a d j r) N.front_onSupport N.back_onSupport

/-- Every internal necklace participates in the actual normalized comparison. -/
def compare : evaluate (supportedFamily F a d j r) ⟶
    presentation F a d j r N ⋙ evaluate (normalizedFamily F a d j r N) :=
  JTSupportedNormalizedEvaluation.compare N.data (incl F a d j r)
    (N.middle_onSupport F a d j r) N.front_onSupport N.back_onSupport
    (supportedPadded F a d j r)

/-- The comparison does not change the homotopy type of the full presentation. -/
theorem presentation_weak : HomotopicalAlgebra.WeakEquivalence
    (nerveMap (presentation F a d j r N)) :=
  JTSupportedNormalizedEvaluation.presentation_weak N.data (incl F a d j r)
    (N.middle_onSupport F a d j r) N.front_onSupport N.back_onSupport

/-- The other side of the full supported span is the canonical point-center cone. -/
def evaluation_toPoint : evaluate (supportedFamily F a d j r) ⟶
    (Functor.const _).obj (center W (jointCoefficient (Q := Q) j)) :=
  JTSupportedNormalizedEvaluation.evaluation_toPoint (W := W)
    (z := jointCoefficient (Q := Q) j) (supportedPadded F a d j r)

end
end DaggerModels.PartII.JTJointBeadNormalizedEvaluation
