import DaggerModelsPartII.JTSharedInsertionCoarseSupportedEvaluation
import DaggerModelsPartII.JTSharedInsertionCoarseWhiskeredOldEvaluation
import DaggerModelsPartII.JTSharedInsertionCoarseEvaluation

/-!
# Retarget the complete zero-endpoint comparison to the existing coarse evaluation

The full old-whiskered evaluator compares to the independently checked coarse
evaluator along its exact complete presentation map. Compose both presentation
maps and both natural comparisons, retaining the strict source triangles.
All original Q/endpoints/time and every internal necklace are retained.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSharedInsertionCoarseSupportedComparison

open JTParametrizedTargetFamilies (Family)
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex


private abbrev J := GroupoidSimplex.parameter
private abbrev std := SSet.stdSimplex.{0}

private def FactorEquation {I : Type} [SmallCategory I] (W : Source) (x z y : Vertex W)
    (M : I ⥤ DecoratedNecklaceHomDiagram.Index W z z) (P R : I ⥤ NecklaceCode)
    (O : JTSupportedPathWhiskeredDiagram.Surroundings W x z y M P R)
    (t : I ⥤ SimplexCategory) {Y : I ⥤ SSet.{0}}
    (pi : Y ⟶ JTSupportedPathWhiskeredGraph.oldProduct W x z y M P R O t)
    (theta : Y ⟶ JTParametrizedTargetFamilyComparison.degrees M ⋙ J)
    (S : I ⥤ SimplexCategory) (u : S ⟶ JTParametrizedTargetFamilyComparison.degrees M)
    (q : ∀ a : I, Limits.pullback
      (pi.app a ≫ CartesianMonoidalCategory.fst (NecklaceCode.wedge (P.obj a)
        (NecklaceCode.wedge ((JTParametrizedTargetFamilies.codes M).obj a)
          (R.obj a))).toSSet (J.obj (t.obj a)))
      (tripleRightU (P.obj a) ((JTParametrizedTargetFamilies.codes M).obj a) (R.obj a)) ⟶
        J.obj (S.obj a)) : Prop :=
  ∀ a : I, Limits.pullback.fst
    (pi.app a ≫ CartesianMonoidalCategory.fst (NecklaceCode.wedge (P.obj a)
      (NecklaceCode.wedge ((JTParametrizedTargetFamilies.codes M).obj a)
        (R.obj a))).toSSet (J.obj (t.obj a)))
    (tripleRightU (P.obj a) ((JTParametrizedTargetFamilies.codes M).obj a) (R.obj a)) ≫
      theta.app a = q a ≫ J.map (u.app a)

private def sourceCat {C D : Type} [SmallCategory C] [SmallCategory D]
    (_f : C ⥤ D) : Cat.{0, 0} := Cat.of C

section GenericZero

open CartesianMonoidalCategory
open JTParametrizedTargetFamilies (codes)
open JTParametrizedTargetFamilyComparison (degrees)

variable {I : Type} [SmallCategory I] (W : Source) (x z y : Vertex W)
variable (M : I ⥤ DecoratedNecklaceHomDiagram.Index W z z)
variable (S : I ⥤ SimplexCategory) (u : S ⟶ degrees M)
variable (hs : ∀ a : I, std.map (u.app a) ≫ JTSupportedOrderedCoefficientChoices.old W z M a =
  JTSupportedOrderedCoefficientChoices.supportedConstant W z M S a)
variable (P R : I ⥤ NecklaceCode)
variable (O : JTSupportedPathWhiskeredDiagram.Surroundings W x z y M P R)
variable (t : I ⥤ SimplexCategory) {Y : I ⥤ SSet.{0}}
variable (pi : Y ⟶ JTSupportedPathWhiskeredGraph.oldProduct W x z y M P R O t)
variable (theta : Y ⟶ degrees M ⋙ J)
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (c : codes (JTSupportedPathWhiskeredGraph.oldLabels W x z y M P R O) ⟶
  (Functor.const I).obj Q.code)
private abbrev T (a : I) := NecklaceCode.wedge (P.obj a)
  (NecklaceCode.wedge ((codes M).obj a) (R.obj a))
private abbrev H (a : I) := pi.app a ≫ fst (T W z M P R a).toSSet (J.obj (t.obj a))
variable (oldRaw : ∀ a : I, lift (H W x z y M P R O t pi a) (theta.app a) ≫
  JTNecklaceLabelRealization.realizedLabel (T W z M P R a).toSSet W ((degrees M).obj a)
    (SSet.yonedaEquiv (JTComposedPrismLabels.coefficient
      (JTThreePieceLabelOperators.coefficients
        (JTSupportedPathWhiskeredGraph.oldData W x z y M P R O a)))) =
  H W x z y M P R O t pi a ≫ (c.app a).map ≫ Q.map)
variable (middleQ : ∀ a : I, Limits.pullback (H W x z y M P R O t pi a)
  (tripleRightU (P.obj a) ((codes M).obj a) (R.obj a)) ⟶ J.obj (S.obj a))
variable (factor : FactorEquation W x z y M P R O t pi theta S u middleQ)
variable (hu : ∀ a : I, Mono (u.app a))

private def oldCat := sourceCat
  (JTSupportedPathWhiskeredZeroEvaluation.oldEvaluation W x z y M P R O t pi theta Q c oldRaw)
private def zeroCat := sourceCat
  (JTSupportedPathWhiskeredZeroEvaluation.endpointEvaluation W x z y M S u hs P R O
    t pi theta Q c oldRaw middleQ factor hu)
private def oldEval : oldCat W x z y M P R O t pi theta Q c oldRaw ⥤
    JTGraphFactoredPresentation.TargetComma Q :=
  JTSupportedPathWhiskeredZeroEvaluation.oldEvaluation W x z y M P R O t pi theta Q c oldRaw
private def zeroEval : zeroCat W x z y M S u hs P R O t pi theta Q c
    oldRaw middleQ factor hu ⥤ JTGraphFactoredPresentation.TargetComma Q :=
  JTSupportedPathWhiskeredZeroEvaluation.endpointEvaluation W x z y M S u hs P R O
    t pi theta Q c oldRaw middleQ factor hu
private def zeroMap : zeroCat W x z y M S u hs P R O t pi theta Q c
    oldRaw middleQ factor hu ⥤ oldCat W x z y M P R O t pi theta Q c oldRaw :=
  JTSupportedPathWhiskeredZeroEvaluation.toOldPresentation W x z y M S u hs P R O
    t pi theta Q c
private def zeroEta : zeroEval W x z y M S u hs P R O t pi theta Q c
    oldRaw middleQ factor hu ⟶
      zeroMap W x z y M S u hs P R O t pi theta Q c oldRaw middleQ factor hu ⋙
        oldEval W x z y M P R O t pi theta Q c oldRaw :=
  JTSupportedPathWhiskeredZeroEvaluation.evaluationComparison W x z y M S u hs P R O
    t pi theta Q c oldRaw middleQ factor hu

variable {B : Type} [SmallCategory B]
variable (q : oldCat W x z y M P R O t pi theta Q c oldRaw ⥤ B)
variable (target : B ⥤ JTGraphFactoredPresentation.TargetComma Q)
variable (kappa : oldEval W x z y M P R O t pi theta Q c oldRaw ⟶ q ⋙ target)

private def presentationGeneric :=
  zeroMap W x z y M S u hs P R O t pi theta Q c oldRaw middleQ factor hu ⋙ q
private def comparisonGeneric :
    zeroEval W x z y M S u hs P R O t pi theta Q c oldRaw middleQ factor hu ⟶
      presentationGeneric W x z y M S u hs P R O t pi theta Q c
        oldRaw middleQ factor hu q ⋙ target :=
  zeroEta W x z y M S u hs P R O t pi theta Q c oldRaw middleQ factor hu ≫
    Functor.whiskerLeft
      (zeroMap W x z y M S u hs P R O t pi theta Q c oldRaw middleQ factor hu) kappa ≫
    (Functor.associator
      (zeroMap W x z y M S u hs P R O t pi theta Q c oldRaw middleQ factor hu)
      q target).inv

private theorem weakGeneric
    (hp : WeakEquivalence (nerveMap
      (zeroMap W x z y M S u hs P R O t pi theta Q c oldRaw middleQ factor hu)))
    (hq : WeakEquivalence (nerveMap q)) :
    WeakEquivalence (nerveMap (presentationGeneric W x z y M S u hs P R O t pi theta Q c
      oldRaw middleQ factor hu q)) := by
  letI := hp
  letI := hq
  change WeakEquivalence (nerveMap
    (zeroMap W x z y M S u hs P R O t pi theta Q c oldRaw middleQ factor hu) ≫ nerveMap q)
  infer_instance

end GenericZero

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

private abbrev z := JTParametrizedBeadGraph.jointCoefficient (W := W) (x := x) (y := y)
  (Q := Q) j
private abbrev M := JTSharedInsertionCoarseWhiskeredData.middleLabels
  (W := W) (x := x) (y := y) F j
private abbrev S := JTSharedInsertionCoarseMiddleSupport.supports
  (W := W) (x := x) (y := y) F j
private abbrev u := JTSharedInsertionCoarseMiddleSupport.inclusion
  (W := W) (x := x) (y := y) F j
private abbrev hs := JTSharedInsertionCoarseMiddleSupport.coefficient_onSupport
  (W := W) (x := x) (y := y) F j
private abbrev P := JTSharedInsertionCoarseWhiskeredData.leftNative
  (W := W) (x := x) (y := y) F j
private abbrev R := JTSharedInsertionCoarseWhiskeredData.rightNative
  (W := W) (x := x) (y := y) F j
private abbrev O := JTSharedInsertionCoarseWhiskeredData.surroundings
  (W := W) (x := x) (y := y) F j
private abbrev oldTime := JTSharedInsertionCoarseWhiskeredGraph.oldTime
  (W := W) (x := x) (y := y) F j
private abbrev oldPi := JTSharedInsertionCoarseWhiskeredGraph.projection
  (W := W) (x := x) (y := y) F j
private abbrev oldTheta := JTSharedInsertionCoarseWhiskeredGraph.parameter
  (W := W) (x := x) (y := y) F j
private abbrev targetNative := JTSharedInsertionCoarseWhiskeredGraph.target
  (W := W) (x := x) (y := y) F j
private abbrev oldRaw := JTSharedInsertionCoarseWhiskeredGraph.oldRaw
  (W := W) (x := x) (y := y) F j
private abbrev middleQ (p : JTSharedInsertionChoices.Index (W := W) (x := x) (y := y) F j) :=
  (JTSharedInsertionCoarseMiddleParameter.factor (W := W) (x := x) (y := y) F j).app p
private abbrev hu := JTSharedInsertionCoarseMiddleSupport.inclusion_mono
  (W := W) (x := x) (y := y) F j

set_option maxHeartbeats 400000 in
private def actualFactor : FactorEquation W x (z (Q := Q) j) y
    (M F j) (P F j) (R F j) (O F j) (oldTime F j) (oldPi F j) (oldTheta F j)
    (S F j) (u F j) (middleQ F j) :=
  JTSharedInsertionCoarseMiddleParameter.factor_incl_app
    (W := W) (x := x) (y := y) F j

/-- The entire zero presentation followed by the checked old-to-coarse presentation map. -/
def presentation := presentationGeneric W x (z (Q := Q) j) y
  (M F j) (S F j) (u F j) (hs F j) (P F j) (R F j) (O F j)
  (oldTime F j) (oldPi F j) (oldTheta F j) Q (targetNative F j)
  (oldRaw F j) (middleQ F j) (actualFactor F j) (hu F j)
  (JTSharedInsertionCoarseWhiskeredOldEvaluation.presentation
    (W := W) (x := x) (y := y) F j)

/-- Complete evaluation comparison with the literal EXISTING coarse evaluator as target. -/
def comparison := comparisonGeneric W x (z (Q := Q) j) y
  (M F j) (S F j) (u F j) (hs F j) (P F j) (R F j) (O F j)
  (oldTime F j) (oldPi F j) (oldTheta F j) Q (targetNative F j)
  (oldRaw F j) (middleQ F j) (actualFactor F j) (hu F j)
  (JTSharedInsertionCoarseWhiskeredOldEvaluation.presentation
    (W := W) (x := x) (y := y) F j)
  (JTSharedInsertionCoarseEvaluation.evaluation
    (W := W) (x := x) (y := y) F j)
  (JTSharedInsertionCoarseWhiskeredOldEvaluation.comparison
    (W := W) (x := x) (y := y) F j)

/-- The complete comparison source is weak under the original injective fibrancy. -/
def presentation_weak
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :=
  weakGeneric W x (z (Q := Q) j) y
    (M F j) (S F j) (u F j) (hs F j) (P F j) (R F j) (O F j)
    (oldTime F j) (oldPi F j) (oldTheta F j) Q (targetNative F j)
    (oldRaw F j) (middleQ F j) (actualFactor F j) (hu F j)
    (JTSharedInsertionCoarseWhiskeredOldEvaluation.presentation
      (W := W) (x := x) (y := y) F j)
    (JTSharedInsertionCoarseSupportedEvaluation.zeroToOld_weak
      (W := W) (x := x) (y := y) F j hW)
    (JTSharedInsertionCoarseWhiskeredOldEvaluation.presentation_weak
      (W := W) (x := x) (y := y) F j)

end
end DaggerModels.PartII.JTSharedInsertionCoarseSupportedComparison
