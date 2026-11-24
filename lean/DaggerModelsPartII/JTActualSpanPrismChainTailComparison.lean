import DaggerModelsPartII.JTActualSpanPrismChainEvaluation
import DaggerModelsPartII.JTReindexedPrismChainComparison
import DaggerModelsPartII.JTGraphSpanSupportCriterion

/-! The realized moving-chain evaluation of an actual finite span. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels DaggerNerveHomotopy
open DaggerChosenRigidificationNecklace DaggerSSetGluing
open DaggerOriginalProductGadget (pointMap)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTActualSpanPrismChainEvaluation

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTActualSpanFamilySection (actualFamily actualSpans)
open JTOrderedLabelPaddingPrismChainCylinder
  (commonEvaluation compareReindexedToTail compareRealized)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : Vertex W}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (A : (nerve (TargetComma Q)).Subcomplex)
variable (P : ObjectProperty (JTSemisimplicialSpanEvaluation.Presentation Q A))

private abbrev originalEval :=
  P.ι ⋙ JTSemisimplicialSpanEvaluation.evaluation Q A (JTGraphSpanEvaluation.fullEvaluation Q)

private abbrev tailOfSpan := JTGraphSpanFamily.tail (TargetComma Q)
private abbrev tail := actualSpans Q A P ⋙ tailOfSpan (Q := Q)

/-- The common evaluation on the actual finite cover maps to the original span tail. -/
def commonToTail :
    commonEvaluation (actualFamily Q A P) ⟶ projection Q A P ⋙ tail Q A P := by
  let h := compareReindexedToTail (JTGraphSpanLift.spanFamily Q) (actualSpans Q A P)
    (tailOfSpan (Q := Q)) (JTActualSpanFamilySection.parametrizedFullComparison Q)
  exact h ≫ eqToHom (Functor.assoc (projection Q A P) (actualSpans Q A P) (tailOfSpan (Q := Q)))

private def originalToTail :
    projection Q A P ⋙ originalEval Q A P ⟶ projection Q A P ⋙ tail Q A P :=
  Functor.whiskerLeft (projection Q A P)
    (eqToHom (JTActualSpanFamilySection.originalEvaluation_eq Q A P).symm ≫
      JTActualSpanFamilySection.originalComparison Q A P)

private theorem pasteComparison {B C : Type} [SmallCategory B] [SmallCategory C]
    {o r c t : B ⥤ C} (h₁ : o ⟶ t) (h₂ : c ⟶ t) (h₃ : c ⟶ r) :
    NatTransZigzag o r :=
  .trans _ _ _ (.rel _ _ ⟨h₁⟩)
    (.trans _ _ _ (.symm _ _ (.rel _ _ ⟨h₂⟩)) (.rel _ _ ⟨h₃⟩))

/-- The full realized evaluation compares to the unchanged finite span evaluation. -/
theorem original_comparison :
    NatTransZigzag (projection Q A P ⋙ originalEval Q A P) (evaluation Q A P) :=
  pasteComparison (originalToTail Q A P) (commonToTail Q A P)
    (compareRealized (actualFamily Q A P))

local instance : ModelCategory Source := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ

/-- The factor condition for the realized full evaluation on the actual finite covers. -/
def RealizedFiniteFactors : Prop :=
  ∀ (W : Source), Localization.localObject SegalLocalizers.localizingFamily W →
    ∀ (x y : Vertex W) (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
      (A : (nerve (TargetComma Q)).Subcomplex), A.toSSet.IsFinite →
      ∀ (P : ObjectProperty (JTSemisimplicialSpanEvaluation.Presentation Q A)),
        Finite P.FullSubcategory →
        ∃ (E : Cat.{0, 0}) (F : Presentation Q A P ⥤ E) (G : E ⥤ TargetComma Q),
          GW (pointMap (nerve E)) ∧ NatTransZigzag (evaluation Q A P) (F ⋙ G)

/-- Weakly contractible factors of these realized evaluations imply the original Theorem C. -/
theorem theoremC_of_realized_factors (h : RealizedFiniteFactors) : TheoremCStatement.statement := by
  apply JTGraphSpanSupportCriterion.theoremC_of_support_nullhomotopies
  intro W hW x y Q A hA
  apply FiniteLastVertexSupport.of_finite_full_weak_cover_factors
  intro P hP
  obtain ⟨E, F, G, hE, e⟩ := h W hW x y Q A hA P hP
  exact ⟨Cat.of (Presentation Q A P), E, projection Q A P, F, G,
    projection_weak Q A P hW.1, hE, .trans _ _ _ (original_comparison Q A P) e⟩

end

end DaggerModels.PartII.JTActualSpanPrismChainEvaluation
