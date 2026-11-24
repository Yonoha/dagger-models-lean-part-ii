import DaggerModelsPartII.JTOrderedLabelJointInsertion
import DaggerModelsPartII.JTPrismJointOrderedLabel

/-! Insert the actual supported label from the joint of a fixed target. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTOrderedLabelJointInsertion

open ReversalDiscreteFreeColimits OrderedNecklaceVertexPoints
open JTParametrizedTargetFamilies (Family)
open JTParametrizedBeadGraph (jointCoefficient fullBeadSupport fullBeadSupportInclusion
  beadLabel restrictedBeadLabel_at_joint)
open JTProjectiveOrderedFiberComparison (row)

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
variable (p : (single d).toSSet ⟶
  (JTTargetIntervalPullback.sourceInterval (F.collapse.app a) j j le_rfl).toSSet)

private abbrev native := p ≫ JTTargetIntervalGluing.middleInclusion (F.collapse.app a) j
private abbrev k := fullBeadSupport F a d (native F a d j p)
private abbrev incl := fullBeadSupportInclusion F a d (native F a d j p)
private abbrev z : Vertex W := jointCoefficient (Q := Q) j

variable {T U : NecklaceCode}
variable (b : JTOrderedLabelBinaryGlue.Inputs W T U (k F a d j p) x (z (Q := Q) j) y)

set_option maxHeartbeats 800000 in
/-- With the actual full-time support used as the common degree, the inserted
middle coefficient is the restriction of the original overlap bead label. -/
theorem coefficient_from_overlap :
    JTOrderedLabelBinaryGlue.coefficient W x y (wedge T (wedge (single d) U)) (k F a d j p)
        (OrderedLabelElements.label W (boundaryPoint W x y) (index (single d) b)) ≫
          diagramMappingPrecomp (discreteFree.{0}.map (tripleRightU T (single d) U)) W =
      SSet.stdSimplex.{0}.map (incl F a d j p) ≫
        SSet.yonedaEquiv.symm (beadLabel (a := a) d (native F a d j p)) := by
  rw [coefficient_middle]
  exact (restrictedBeadLabel_at_joint F a d j p).symm

end

end DaggerModels.PartII.JTOrderedLabelJointInsertion
