import DaggerModelsPartII.JTJointOverlapPrismDiagram
import DaggerModelsPartII.JTPaddedPointTargetFamily
import DaggerModelsPartII.JTPrismJointOrderedLabel

/-!
# The decorated evaluation of the full overlap at an actual target joint
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace DaggerSSetGluing DaggerOriginalProductGadget

namespace DaggerModels.PartII.JTJointPaddedOverlapEvaluation

open JTJointOverlapPrismDiagram (overlapSimplices)
open JTParametrizedProductSimplices (Index base degree simplex)
open JTParametrizedBeadGraph (jointCoefficient)
open JTParametrizedTargetFamilies (Family Presentation evaluate)
open JTPointTargetEvaluationCone (pointTarget)
open JTGraphFactoredPresentation (TargetComma)
open JTTargetJointMarks (Joint)
open JTOrderedLabelCoefficientPadding (embedding)
open JTParametrizedBeadGraph (beadLabel fullBeadSupport fullBeadSupportInclusion
  supportedOverlapLabel_coefficient)
open JTConstantOrderedLabel (constantCoefficient)
open ReversalDiscreteFreeColimits

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Input (W : Source) := JTReversalInput.ordinaryInput.obj W
private abbrev Raw (W : Source) := OrdinaryJTRealization.realization.obj (Input W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter

variable {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable (j : Joint Q.code)

/-- The raw map of the point target for the new labels is the original joint map. -/
theorem target_map :
    (pointTarget W (jointCoefficient (Q := Q) j)).map =
      JTPrismJointNormalization.jointRaw (Q := Q) j := by
  apply SSet.yonedaEquiv.injective
  change SSet.yonedaEquiv
      (SSet.yonedaEquiv.symm (rawVertex W (jointCoefficient (Q := Q) j))) = _
  rw [Equiv.apply_symm_apply]
  change (JTRawVertexRecovery.zeroVertexEquiv (Input W))
      ((JTRawVertexRecovery.zeroVertexEquiv (Input W)).symm _) = _
  exact Equiv.apply_symm_apply _ _

variable {A : Type} [SmallCategory A]
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory}
variable (F : Family Q L time)

private abbrev X := overlapSimplices F j
private abbrev D := degree (X j F)
private abbrev timeOnOverlap := base (X j F) ⋙ time
private abbrev k := base (X j F) ⋙ JTJointRelativeGraphFamily.coefficient (L := L)
private abbrev originalParameter := JTJointOverlapPrismDiagram.parameter F j

/-- The padded labels form a diagram on every horizontal simplex in the actual overlap. -/
abbrev labels :=
  JTPaddedPointTargetFamily.labels W (jointCoefficient (Q := Q) j) (D j F) (k j F)

/-- The decorated family uses the entire original parameter on the full timed overlap. -/
abbrev family :
    Family (pointTarget W (jointCoefficient (Q := Q) j)) (labels j F) (timeOnOverlap j F) :=
  JTPaddedPointTargetFamily.family W (jointCoefficient (Q := Q) j) (originalParameter j F)

/-- Both outer marks are preserved by the original horizontal, time and label operators. -/
abbrev synchronized : JTMarkedFiniteParametrizedTargetFamilies.Synchronized (timeOnOverlap j F)
    (pointTarget W (jointCoefficient (Q := Q) j)) :=
  JTPaddedPointTargetFamily.synchronized W (jointCoefficient (Q := Q) j) (originalParameter j F)

/-- The interior comparison keeps the original parameter at every time and
embeds its original coefficient ordinal in the padded ordinal. -/
theorem interior_parameter (a : Index (X j F)) :
    (JTPaddedPointTargetFamily.interior (D := D j F) a ⊗ₘ
      𝟙 (J.obj ((timeOnOverlap j F).obj a))) ≫ (family j F).parameter a =
        (originalParameter j F).app a ≫ J.map (embedding ((k j F).obj a)) :=
  JTPaddedPointTargetFamily.interior_parameter W (jointCoefficient (Q := Q) j)
    (originalParameter j F) a

private abbrev nativeChart (a : Index (X j F)) :=
  (NecklaceCode.singleIso ((D j F).obj a).len).hom ≫ simplex (X j F) a

private abbrev originalBead (a : Index (X j F)) :=
  nativeChart j F a ≫ JTTargetIntervalGluing.middleInclusion (F.collapse.app a.base) j

private abbrev usedInclusion (a : Index (X j F)) :=
  fullBeadSupportInclusion F a.base ((D j F).obj a).len (originalBead j F a)

private abbrev paddedChart (a : Index (X j F)) :=
  (NecklaceCode.singleIso ((D j F).obj a).len).hom ≫
    JTPaddedPointTargetFamily.interior (D := D j F) a

private abbrev paddedCode (a : Index (X j F)) :=
  JTPaddedSingleNecklaceDiagram.code.obj ((D j F).obj a)

set_option maxHeartbeats 900000 in
/-- The padded label agrees with the original label on the native interior
and on every coefficient vertex used anywhere in its full time prism. -/
theorem interior_support_coefficient (a : Index (X j F)) :
    (SSet.stdSimplex.map (usedInclusion j F a ≫ embedding ((k j F).obj a)) ≫
      constantCoefficient W (jointCoefficient (Q := Q) j) (paddedCode j F a)
        ((JTPaddedPrismParameter.padded (k j F)).obj a)) ≫
        diagramMappingPrecomp (discreteFree.map (paddedChart j F a)) W =
    SSet.stdSimplex.map (usedInclusion j F a) ≫
      SSet.yonedaEquiv.symm (beadLabel (a := a.base) ((D j F).obj a).len
        (originalBead j F a)) := by
  let T := NecklaceCode.single ((D j F).obj a).len
  let l := fullBeadSupport F a.base ((D j F).obj a).len (originalBead j F a)
  let term := SSet.stdSimplex.isTerminalObj₀.from
  have hc := supportedOverlapLabel_coefficient F a.base ((D j F).obj a).len j
    (nativeChart j F a)
  rw [JTConstantOrderedLabel.coefficient_constantLabel] at hc
  rw [← hc]
  have hp := JTConstantOrderedLabel.constantCoefficient_ordinal W (jointCoefficient (Q := Q) j)
    (paddedCode j F a) (usedInclusion j F a ≫ embedding ((k j F).obj a))
  calc
    _ = constantCoefficient W (jointCoefficient (Q := Q) j) (paddedCode j F a) _ ≫
        diagramMappingPrecomp (discreteFree.map (paddedChart j F a)) W :=
      congrArg
        (fun f ↦ f ≫ diagramMappingPrecomp (discreteFree.map (paddedChart j F a)) W) hp.symm
    _ = _ := by
      simp only [constantCoefficient, Category.assoc, ← diagramMappingPrecomp_comp,
        ← discreteFree.map_comp]
      exact congrArg (fun f : T.toSSet ⟶ (Δ[0] : SSet.{0}) ↦
        term (SSet.stdSimplex.obj l) ≫ OrderedNecklaceVertexPoints.zeroPoint W
          (jointCoefficient (Q := Q) j) ≫ diagramMappingPrecomp (discreteFree.map f) W)
        (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)

/-- Every internal necklace of the padded overlap evaluates through a weakly contractible
category over the literal joint, for any original parameter on the overlap. -/
theorem exists_contractible_factor :
    ∃ (C : Cat.{0, 0}) (u : Presentation (L := labels j F) (time := timeOnOverlap j F) ⥤ C)
      (v : C ⥤ TargetComma (pointTarget W (jointCoefficient (Q := Q) j))),
      GW (pointMap (nerve C)) ∧ evaluate (family j F) = u ⋙ v :=
  JTPaddedPointTargetFamily.exists_contractible_factor W (jointCoefficient (Q := Q) j)
    (originalParameter j F)

end
end DaggerModels.PartII.JTJointPaddedOverlapEvaluation
