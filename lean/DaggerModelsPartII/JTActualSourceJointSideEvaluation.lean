import DaggerModelsPartII.JTActualSourceJointSupport
import DaggerModelsPartII.JTActualJointSideFamilies
import DaggerModelsPartII.LocalEquivalenceClasses

/-! Actual corrected side evaluations for every source cut over a fixed target joint. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTActualSourceJointSideEvaluation

open JTActualJointSideFamilies (CutSupport)
open JTActualSourceJointSupport (usedDegree usedInclusion usedInclusion_mono timeParameter_factor
  liftedOverlapVertex oldVertexRow_supported_joint)
open JTParametrizedTargetFamilies (Family codes)
open JTTargetJointMarks (Joint)
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)

variable {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {A : Type} [SmallCategory A] {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (a : A) (j : Joint Q.code)
variable (v : Fin (((codes L).obj a).len + 1))
variable (hv : orderMap (F.collapse.app a).map v = j.val)

/-- The literal used face of the whole original timed parameter satisfies the side hypotheses. -/
def support : CutSupport F a j v where
  degree := usedDegree F a j v hv
  inclusion := usedInclusion F a j v hv
  mono := usedInclusion_mono F a j v hv
  timeMap := JTJointTimedEndpointSupport.supportedTimedParameter F a j
    (liftedOverlapVertex F a j v hv)
  time_eq := (timeParameter_factor F a j v hv).symm
  row_eq := oldVertexRow_supported_joint F a j v hv

local instance : ModelCategory Source := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ

variable (hW : Localization.localObject SegalLocalizers.localizingFamily W)

set_option maxHeartbeats 1000000 in
/-- The whole original left cut, with its added endpoint edge, evaluates over the actual left. -/
def leftFamily :=
  JTActualJointSideFamilies.leftFamily F a j v hv (support F a j v hv) hW.1

set_option maxHeartbeats 1000000 in
/-- The whole original right cut, with its added endpoint edge, evaluates over the actual right. -/
def rightFamily :=
  JTActualJointSideFamilies.rightFamily F a j v hv (support F a j v hv) hW.1

end
end DaggerModels.PartII.JTActualSourceJointSideEvaluation
