import DaggerModelsPartII.JTPrismJointOrderedLabel
import DaggerModelsPartII.JTJointTraceObstruction
import DaggerModelsPartII.JTPointTargetEvaluationCone
import DaggerModelsPartII.JTJointPaddedOverlapEvaluation

/-! The actual timed support and constant ordered label of a bead in a joint fiber. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace DaggerSSetGluing
open DaggerOriginalProductGadget

namespace DaggerModels.PartII.JTJointBeadOverlapRestriction

open JTParametrizedTargetFamilies (Family codes evaluate)
open JTProjectiveOrderedFiberComparison (row)
open JTTargetJointMarks (Joint)
open JTParametrizedBeadGraph (jointCoefficient fullBeadParameter fullBeadSupport
  fullBeadSupportInclusion supportedOverlapIndex supportedOverlapCollapse
  supportedOverlapMap supportedOverlapLabel_coefficient)
open JTPrismRectangle (supportedParameter supportedParameter_factor)
open JTPointTargetEvaluationCone (pointTarget)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev std := SSet.stdSimplex.{0}

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (a : A) (d : ℕ) (j : Joint Q.code)
variable (r : (NecklaceCode.single d).toSSet ⟶
  (JTTargetIntervalPullback.sourceInterval (F.collapse.app a) j j le_rfl).toSSet)

private abbrev native := r ≫ JTTargetIntervalGluing.middleInclusion (F.collapse.app a) j

/-- The original coefficient indices used by the whole timed overlap bead. -/
abbrev usedDegree := fullBeadSupport F a d (native F a d j r)

/-- The chosen full-support parameter of the actual original prism. -/
abbrev timedParameter :
    (Δ[d] : SSet.{0}) ⊗ J.obj (time.obj a) ⟶ J.obj (usedDegree F a d j r) :=
  supportedParameter (fullBeadParameter F a d (native F a d j r))

/-- The full timed parameter factors through the original coefficient ordinal. -/
theorem timedParameter_fac :
    timedParameter F a d j r ≫ J.map
      (fullBeadSupportInclusion F a d (native F a d j r)) =
        fullBeadParameter F a d (native F a d j r) :=
  supportedParameter_factor _

/-- The actual ordered source label, with its coefficient restricted to all
indices used by the timed bead. -/
abbrev label := supportedOverlapIndex F a d j r

/-- The canonical decorated arrow from the supported label to the common point. -/
def toPoint : label F a d j r ⟶
    JTPointTargetEvaluationCone.pointLabel W (jointCoefficient (Q := Q) j) :=
  supportedOverlapCollapse F a d j r

/-- Equality in the original mapping space between the supported source label
and the exact restriction of the original bead coefficient. -/
theorem coefficient_eq_original :
    JTOrderedLabelBinaryGlue.coefficient W (jointCoefficient (Q := Q) j)
      (jointCoefficient (Q := Q) j) (NecklaceCode.single d) (usedDegree F a d j r)
      (JTConstantOrderedLabel.constantLabel W (jointCoefficient (Q := Q) j)
        (NecklaceCode.single d) (usedDegree F a d j r)) =
      std.map (fullBeadSupportInclusion F a d (native F a d j r)) ≫
        SSet.yonedaEquiv.symm
          (JTParametrizedBeadGraph.beadLabel (a := a) d (native F a d j r)) :=
  supportedOverlapLabel_coefficient F a d j r

section Operators

variable {a d r} {b : A} {e : ℕ}
variable {r' : (NecklaceCode.single e).toSSet ⟶
  (JTTargetIntervalPullback.sourceInterval (F.collapse.app b) j j le_rfl).toSSet}
variable (f : a ⟶ b) (u : ⦋d⦌ ⟶ ⦋e⦌)
variable (h₀ : u.toOrderHom 0 = 0) (h₁ : u.toOrderHom (Fin.last d) = Fin.last e)
variable (h : (NecklaceCode.singleIso d).inv ≫ native F a d j r ≫
    ((codes L).map f).map =
  std.map u ≫ (NecklaceCode.singleIso e).inv ≫ native F b e j r')

/-- The exact source bead, time, and coefficient operators give an arrow
between the actual supported constant labels. -/
def labelMap : label F a d j r ⟶ label F b e j r' :=
  supportedOverlapMap F j f u h₀ h₁ h

/-- The same operator commutes with the complete supported time parameter. -/
theorem timedParameter_map :
    (std.map u ⊗ₘ J.map (time.map f)) ≫ timedParameter F b e j r' =
      timedParameter F a d j r ≫ J.map
        (JTParametrizedBeadGraph.fullBeadSupportMap F f u
          (by simpa only [Category.assoc] using h)) :=
  JTParametrizedBeadGraph.supportedFullBeadParameter_map F f u
    (by simpa only [Category.assoc] using h)

end Operators

end
end DaggerModels.PartII.JTJointBeadOverlapRestriction
