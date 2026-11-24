import DaggerModelsPartII.JTSharedInsertionCoarseSupportedPresentation
import DaggerModelsPartII.JTSharedInsertionCoarseMiddleParameter
import DaggerModelsPartII.JTSupportedPathWhiskeredOneEvaluation

/-!
# The actual supported middle comparison of complete evaluations in original Q

All graph, raw, support and GIVEN-parameter factor data are derived from the
original Family and target joint. The zero endpoint compares to the existing
old whiskered graph interface; its identification with the previously checked
coarse evaluator is a separate comparison. The one endpoint compares to the
literal constant-MIDDLE full evaluator. The varying surroundings and entire original time remain.
This does not assert a nullhomotopy of the full original finite span.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSharedInsertionCoarseSupportedEvaluation

open JTParametrizedTargetFamilies (Family)
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

private abbrev J := GroupoidSimplex.parameter

private def FactorEquation {I : Type} [SmallCategory I] (W : Source) (x z y : Vertex W)
    (M : I ⥤ DecoratedNecklaceHomDiagram.Index W z z) (P R : I ⥤ NecklaceCode)
    (O : JTSupportedPathWhiskeredDiagram.Surroundings W x z y M P R)
    (t : I ⥤ SimplexCategory) {Y : I ⥤ SSet.{0}}
    (pi : Y ⟶ JTSupportedPathWhiskeredGraph.oldProduct W x z y M P R O t)
    (theta : Y ⟶ JTParametrizedTargetFamilyComparison.degrees M ⋙ J)
    (S : I ⥤ SimplexCategory) (u : S ⟶ JTParametrizedTargetFamilyComparison.degrees M)
    (q : ∀ a : I, pullback
      (pi.app a ≫ fst (NecklaceCode.wedge (P.obj a)
        (NecklaceCode.wedge ((JTParametrizedTargetFamilies.codes M).obj a)
          (R.obj a))).toSSet (J.obj (t.obj a)))
      (tripleRightU (P.obj a) ((JTParametrizedTargetFamilies.codes M).obj a) (R.obj a)) ⟶
        J.obj (S.obj a)) : Prop :=
  ∀ a : I, pullback.fst
    (pi.app a ≫ fst (NecklaceCode.wedge (P.obj a)
      (NecklaceCode.wedge ((JTParametrizedTargetFamilies.codes M).obj a)
        (R.obj a))).toSSet (J.obj (t.obj a)))
    (tripleRightU (P.obj a) ((JTParametrizedTargetFamilies.codes M).obj a) (R.obj a)) ≫
      theta.app a = q a ≫ J.map (u.app a)

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

private abbrev oldRaw := JTSharedInsertionCoarseWhiskeredGraph.oldRaw F j
private abbrev q (p : JTSharedInsertionChoices.Index F j) :=
  (JTSharedInsertionCoarseMiddleParameter.factor F j).app p
private abbrev hq := JTSharedInsertionCoarseMiddleParameter.factor_incl_app F j
private abbrev hu := JTSharedInsertionCoarseMiddleSupport.inclusion_mono F j
private abbrev hp := JTSharedInsertionCoarseSupportedLabels.middle_positive F j
private abbrev hπ := JTSharedInsertionCoarseWhiskeredGraph.projection_trivialFibration F j

set_option maxHeartbeats 400000 in
private def actualFactor : FactorEquation W x (z j) y (M F j) (P F j) (R F j) (O F j)
    (oldTime F j) (oldπ F j) (oldθ F j) (S F j) (u F j) (q F j) :=
  hq F j

/-- Evaluate EVERY internal necklace of the full supported graph in SAME original Q. -/
def evaluation := JTSupportedPathWhiskeredRaw.evaluation W x (z j) y
  (M F j) (S F j) (u F j) (hs F j) (P F j) (R F j) (O F j)
  (oldTime F j) (oldπ F j) (oldθ F j) Q (c F j)
  (oldRaw F j) (q F j) (actualFactor F j) (hu F j)

/-- The full zero endpoint presentation, including every internal necklace. -/
abbrev zeroPresentation := JTSupportedPathWhiskeredZeroEvaluation.endpointPresentation
  W x (z j) y (M F j) (S F j) (u F j) (hs F j) (P F j) (R F j) (O F j)
  (oldTime F j) (oldπ F j) (oldθ F j) Q (c F j)

/-- Include the entire zero endpoint in the full path presentation. -/
abbrev zeroInclusion := JTSupportedPathWhiskeredZeroEvaluation.endpointInclusion
  W x (z j) y (M F j) (S F j) (u F j) (hs F j) (P F j) (R F j) (O F j)
  (oldTime F j) (oldπ F j) (oldθ F j) Q (c F j)

/-- Transport every zero-endpoint internal necklace to the existing old presentation. -/
abbrev zeroToOld := JTSupportedPathWhiskeredZeroEvaluation.toOldPresentation
  W x (z j) y (M F j) (S F j) (u F j) (hs F j) (P F j) (R F j) (O F j)
  (oldTime F j) (oldπ F j) (oldθ F j) Q (c F j)

/-- The existing old graph evaluator instantiated by actual F,j and complete raw data. -/
def oldEvaluation := JTSupportedPathWhiskeredZeroEvaluation.oldEvaluation W x (z j) y
  (M F j) (P F j) (R F j) (O F j) (oldTime F j) (oldπ F j) (oldθ F j) Q (c F j)
  (oldRaw F j)

/-- The exact zero-endpoint comparison to the existing full old graph evaluator. -/
def zeroComparison := JTSupportedPathWhiskeredZeroEvaluation.evaluationComparison
  W x (z j) y (M F j) (S F j) (u F j) (hs F j) (P F j) (R F j) (O F j)
  (oldTime F j) (oldπ F j) (oldθ F j) Q (c F j)
  (oldRaw F j) (q F j) (actualFactor F j) (hu F j)

/-- The full time-one endpoint presentation. -/
abbrev onePresentation := JTSupportedPathWhiskeredOneEvaluation.endpointPresentation
  W x (z j) y (M F j) (S F j) (u F j) (hs F j) (P F j) (R F j) (O F j)
  (oldTime F j) (oldπ F j) (oldθ F j) Q (c F j)

/-- Include the entire time-one endpoint in the full path presentation. -/
abbrev oneInclusion := JTSupportedPathWhiskeredOneEvaluation.endpointInclusion
  W x (z j) y (M F j) (S F j) (u F j) (hs F j) (P F j) (R F j) (O F j)
  (oldTime F j) (oldπ F j) (oldθ F j) Q (c F j)

/-- Transport every one-endpoint internal necklace to the constant-middle presentation. -/
abbrev oneToConstant := JTSupportedPathWhiskeredOneEvaluation.toConstantPresentation
  W x (z j) y (M F j) (S F j) (u F j) (hs F j) (P F j) (R F j) (O F j)
  (oldTime F j) (oldπ F j) (oldθ F j) Q (c F j)

/-- The full evaluator with ONLY its middle coefficient replaced by the literal constant. -/
def constantEvaluation := JTWhiskeredMiddleConstantEvaluation.evaluation W x (z j) y
  (M F j) (S F j) (u F j) (hs F j) (P F j) (R F j) (O F j)
  (oldTime F j) (oldπ F j) (oldθ F j) Q (c F j)
  (oldRaw F j) (q F j) (actualFactor F j)

/-- The exact one-endpoint comparison to the full constant-middle evaluation. -/
def oneComparison := JTSupportedPathWhiskeredOneEvaluation.evaluationComparison
  W x (z j) y (M F j) (S F j) (u F j) (hs F j) (P F j) (R F j) (O F j)
  (oldTime F j) (oldπ F j) (oldθ F j) Q (c F j)
  (oldRaw F j) (q F j) (actualFactor F j) (hu F j)

/-- Zero endpoint inclusion is weak on the complete presentation. -/
def zeroInclusion_weak := JTSupportedPathWhiskeredZeroEvaluation.endpointInclusion_weak
  W x (z j) y (M F j) (S F j) (u F j) (hs F j) (P F j) (R F j) (O F j)
  (oldTime F j) (oldπ F j) (oldθ F j) Q (c F j) (hπ F j)

/-- Time-one endpoint inclusion is weak on the complete presentation. -/
def oneInclusion_weak := JTSupportedPathWhiskeredOneEvaluation.endpointInclusion_weak
  W x (z j) y (M F j) (S F j) (u F j) (hs F j) (P F j) (R F j) (O F j)
  (oldTime F j) (oldπ F j) (oldθ F j) Q (c F j) (hπ F j)

/-- The complete zero-to-old presentation map is weak under original fibrancy. -/
def zeroToOld_weak
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :=
  JTSupportedPathWhiskeredZeroEvaluation.toOldPresentation_weak W x (z j) y
    (M F j) (S F j) (u F j) (hs F j) (P F j) (R F j) (O F j)
    (oldTime F j) (oldπ F j) (oldθ F j) Q (c F j) (hu F j) hW (hp F j) (hπ F j)

/-- The complete one-to-constant presentation map is weak under original fibrancy. -/
def oneToConstant_weak
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :=
  JTSupportedPathWhiskeredOneEvaluation.toConstantPresentation_weak W x (z j) y
    (M F j) (S F j) (u F j) (hs F j) (P F j) (R F j) (O F j)
    (oldTime F j) (oldπ F j) (oldθ F j) Q (c F j) (hu F j) hW (hp F j) (hπ F j)

end
end DaggerModels.PartII.JTSharedInsertionCoarseSupportedEvaluation
