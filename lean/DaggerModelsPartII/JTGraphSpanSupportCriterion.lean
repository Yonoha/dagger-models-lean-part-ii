import DaggerModelsPartII.JTGraphSpanEvaluation
import DaggerModelsPartII.JTSemisimplicialSpanEvaluation
import DaggerModelsPartII.FiniteSupportCategoryFactor
import DaggerModelsPartII.JTRezkRecognitionFiniteFactor

/-! A finite-support criterion for the exact original span evaluation. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerSSetGluing DaggerNerveHomotopy
open DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTGraphSpanSupportCriterion

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

local instance : ModelCategory Source := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ

/-- Finite-support nullhomotopies on the exact injective-phase evaluation. -/
def FullSupportNullhomotopies : Prop :=
  ∀ (W : Source), Localization.localObject SegalLocalizers.localizingFamily W →
    ∀ (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
      (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
      (A : (nerve (TargetComma Q)).Subcomplex), A.toSSet.IsFinite →
      FiniteLastVertexSupport.SupportNullhomotopies
        (JTSemisimplicialSpanEvaluation.evaluation Q A
          (JTGraphSpanEvaluation.fullEvaluation Q))

/-- The finite-support condition on the exact span evaluation implies Theorem C. -/
theorem theoremC_of_support_nullhomotopies
    (h : FullSupportNullhomotopies) :
    TheoremCStatement.statement := by
  apply JTRezkRecognitionFiniteFactor.theoremC_of_finite_comma_nullhomotopies
  intro W hW x y Q A hA
  exact JTSemisimplicialSpanEvaluation.inclusion_nullhomotopic Q A hA
    (JTGraphSpanEvaluation.fullComparison Q) (h W hW x y Q A hA)

/-- Weakly contractible factors on the finite-object full subcategories of the evaluation. -/
def FiniteFullFactors : Prop :=
  ∀ (W : Source), Localization.localObject SegalLocalizers.localizingFamily W →
    ∀ (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
      (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
      (A : (nerve (TargetComma Q)).Subcomplex), A.toSSet.IsFinite →
      ∀ (P : ObjectProperty (JTSemisimplicialSpanEvaluation.Presentation Q A)),
        Finite P.FullSubcategory →
        ∃ (E : Cat.{0, 0}) (F : P.FullSubcategory ⥤ E)
          (G : E ⥤ TargetComma Q),
          GW (pointMap (nerve E)) ∧
            NatTransZigzag
              (P.ι ⋙ JTSemisimplicialSpanEvaluation.evaluation Q A
                (JTGraphSpanEvaluation.fullEvaluation Q)) (F ⋙ G)

/-- Finite full-subcategory factors supply the finite-support nullhomotopies. -/
theorem support_of_finite_full_factors (h : FiniteFullFactors) :
    FullSupportNullhomotopies := by
  intro W hW x y Q A hA
  exact FiniteLastVertexSupport.of_finite_full_factors
    (JTSemisimplicialSpanEvaluation.evaluation Q A
      (JTGraphSpanEvaluation.fullEvaluation Q))
    (h W hW x y Q A hA)

/-- The finite full-subcategory factor condition implies Theorem C. -/
theorem theoremC_of_finite_full_factors
    (h : FiniteFullFactors) :
    TheoremCStatement.statement :=
  theoremC_of_support_nullhomotopies (support_of_finite_full_factors h)

end
end DaggerModels.PartII.JTGraphSpanSupportCriterion
