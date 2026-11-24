import DaggerModelsPartII.JTSharedInsertionCoarseSupportedLabels
import DaggerModelsPartII.JTSharedInsertionCoarseWhiskeredGraph
import DaggerModelsPartII.JTSupportedPathWhiskeredRaw

/-!
# The complete presentation over the actual supported coarse path

Keep all lifts of the given whole coarse graph through the supported path
coefficient chains. Reduce the COMPLETE inverse images of both endpoint lines.
The existing graph and path-cover theorems give a weak projection to precisely
the original shared insertion choices. This source construction does not yet
assert its evaluation or a contraction of the original finite span.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSharedInsertionCoarseSupportedPresentation

open JTParametrizedTargetFamilies (Family)
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

private abbrev z := JTParametrizedBeadGraph.jointCoefficient (Q := Q) j
private abbrev M := JTSharedInsertionCoarseWhiskeredData.middleLabels F j
private abbrev S := JTSharedInsertionCoarseMiddleSupport.supports F j
private abbrev u := JTSharedInsertionCoarseMiddleSupport.inclusion F j
private abbrev hs := JTSharedInsertionCoarseMiddleSupport.coefficient_onSupport F j
private abbrev P := JTSharedInsertionCoarseWhiskeredData.leftNative F j
private abbrev R := JTSharedInsertionCoarseWhiskeredData.rightNative F j
private abbrev O := JTSharedInsertionCoarseWhiskeredData.surroundings F j
private abbrev oldTime := JTSharedInsertionCoarseWhiskeredGraph.oldTime F j
private abbrev oldπ := JTSharedInsertionCoarseWhiskeredGraph.projection F j
private abbrev oldθ := JTSharedInsertionCoarseWhiskeredGraph.parameter F j
private abbrev c := JTSharedInsertionCoarseWhiskeredGraph.target F j

/-- All old-graph lifts through each full supported coefficient-path chain. -/
abbrev graph := JTSupportedPathWhiskeredGraph.graph W (z j)
  (M F j) (S F j) (u F j) (hs F j) (oldθ F j)

/-- The entire original native/time coordinate of each supported graph point. -/
abbrev projection := JTSupportedPathWhiskeredGraph.projectionNew W x (z j) y
  (M F j) (S F j) (u F j) (hs F j) (P F j) (R F j) (O F j)
  (oldTime F j) (oldπ F j) (oldθ F j)

/-- The actual lifted coefficient parameter, without a chosen natural section. -/
abbrev parameter := JTSupportedPathWhiskeredGraph.parameter W (z j)
  (M F j) (S F j) (u F j) (hs F j) (oldθ F j)

/-- Collapse precisely the complete inverse images of both original endpoint lines. -/
abbrev reduced := JTSupportedPathWhiskeredRaw.reduced W x (z j) y
  (M F j) (S F j) (u F j) (hs F j) (P F j) (R F j) (O F j)
  (oldTime F j) (oldπ F j) (oldθ F j) Q (c F j)

/-- Forget internal necklaces to the complete supported path-chain index. -/
abbrev toChain := JTSupportedPathWhiskeredRaw.toChain W x (z j) y
  (M F j) (S F j) (u F j) (hs F j) (P F j) (R F j) (O F j)
  (oldTime F j) (oldπ F j) (oldθ F j) Q (c F j)

/-- Return to the unchanged original insertion choices, not to Marked or A. -/
abbrev toChoices := JTSupportedPathWhiskeredRaw.toOriginal W x (z j) y
  (M F j) (S F j) (u F j) (hs F j) (P F j) (R F j) (O F j)
  (oldTime F j) (oldπ F j) (oldθ F j) Q (c F j)

/-- The whole internal-necklace presentation weakly covers its path-chain index. -/
def toChain_weak := JTSupportedPathWhiskeredRaw.toChain_weak W x (z j) y
  (M F j) (S F j) (u F j) (hs F j) (P F j) (R F j) (O F j)
  (oldTime F j) (oldπ F j) (oldθ F j) Q (c F j)
  (JTSharedInsertionCoarseWhiskeredGraph.projection_trivialFibration F j)

/-- Under the original injective fibrancy, the entire presentation is weak
over exactly Shared.Index. All hypotheses of the existing theorem are derived. -/
def toChoices_weak
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :=
  JTSupportedPathWhiskeredRaw.toOriginal_weak W x (z j) y
    (M F j) (S F j) (u F j) (hs F j) (P F j) (R F j) (O F j)
    (oldTime F j) (oldπ F j) (oldθ F j) Q (c F j)
    (JTSharedInsertionCoarseMiddleSupport.inclusion_mono F j) hW
    (JTSharedInsertionCoarseSupportedLabels.middle_positive F j)
    (JTSharedInsertionCoarseWhiskeredGraph.projection_trivialFibration F j)

end
end DaggerModels.PartII.JTSharedInsertionCoarseSupportedPresentation
