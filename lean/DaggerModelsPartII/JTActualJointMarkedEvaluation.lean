import DaggerModelsPartII.JTActualJointTargetWedge
import DaggerModelsPartII.JTFiniteNecklaceGraphRefinement
import DaggerModelsPartII.JTMarkedFiniteParametrizedTargetFamilies
import DaggerModelsPartII.JTOrderedLabelJointInsertionEvaluation
import DaggerModelsPartII.JTPrismJointCoefficient

/-! Comparison of joined marked families at an actual joint of the original fixed target. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTActualJointMarkedEvaluation

open JTProjectiveOrderedFiberComparison (row)
open JTFiniteNecklaceGraphRefinement (atRaw)
open JTParametrizedBeadGraph (jointCoefficient)
open JTTargetJointMarks (Joint)
open JTMarkedFiniteParametrizedTargetFamilies (Synchronized)
open JTMarkedJoinJointInsertion
open JTParametrizedTargetFamilies (evaluate)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Input (W : Source) := JTReversalInput.ordinaryInput.obj W
private abbrev Raw (W : Source) := OrdinaryJTRealization.realization.obj (Input W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : Vertex W}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)) (j : Joint Q.code)

private theorem raw_joint :
    JTActualJointTargetWedge.jointVertex Q j = rawVertex W (jointCoefficient (Q := Q) j) := by
  have h : JTActualJointTargetWedge.jointVertex Q j =
      SSet.yonedaEquiv (JTPrismJointNormalization.jointRaw (Q := Q) j) := by
    change JTActualJointTargetWedge.jointVertex Q j = SSet.yonedaEquiv
      (NecklaceCode.pointAt Q.code (ULift.up j.val) ≫ Q.map)
    rw [SSet.yonedaEquiv_comp, NecklaceCode.pointAt_vertex]
    rfl
  rw [h]
  change SSet.yonedaEquiv (JTPrismJointNormalization.jointRaw (Q := Q) j) =
    (JTRawVertexRecovery.zeroVertexEquiv (Input W))
      ((JTRawVertexRecovery.zeroVertexEquiv (Input W)).symm
        (SSet.yonedaEquiv (JTPrismJointNormalization.jointRaw (Q := Q) j)))
  exact ((JTRawVertexRecovery.zeroVertexEquiv (Input W)).apply_symm_apply _).symm

/-- The left cut with both endpoints in the original zero row. -/
def left : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W (jointCoefficient (Q := Q) j)) :=
  atRaw (JTActualJointTargetWedge.left Q j) rfl (raw_joint Q j)

/-- The right cut with the exact same joint coefficient as the left cut. -/
def right : NecklacesOver (Raw W) (rawVertex W (jointCoefficient (Q := Q) j)) (rawVertex W y) :=
  atRaw (JTActualJointTargetWedge.right Q j) (raw_joint Q j) rfl

/-- Cutting and gluing recovers the actual original target over the raw realization. -/
def targetIso : NecklacesOver.wedge (left Q j) (right Q j) ≅ Q :=
  JTActualJointTargetWedge.cutIso Q j

variable {A : Type} [SmallCategory A] {t : A ⥤ SimplexCategory}
variable (F : Synchronized t (left Q j)) (G : Synchronized t (right Q j))
variable (M : A ⥤ NecklaceCode)

/-- The joined evaluation with an arbitrary added middle compares in the original
target comma at the specified joint, with the exact bounds of the two sides. -/
def comparison :=
  expandedMarkedComparisonAfterPostcomp F.upper G.lower F.family G.family
    F.upper_bound G.lower_bound M (targetIso Q j).hom

end
end DaggerModels.PartII.JTActualJointMarkedEvaluation
