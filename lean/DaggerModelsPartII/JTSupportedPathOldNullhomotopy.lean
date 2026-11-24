import DaggerModelsPartII.JTSupportedPathZeroComparison
import DaggerModelsPartII.JTBoundaryNecklaceTwoReindexComparison
import DaggerModelsPartII.JTSupportedPathEvaluationNullhomotopy
import DaggerModelsPartII.FiniteSupportWeakCoverNullhomotopy

/-! Nullhomotopies on complete endpoint presentations of a supported label contraction. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerNerveHomotopy
open DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSupportedPathOldNullhomotopy

open JTProjectiveOrderedFiberComparison (row)
open JTPointTargetEvaluationCone (pointTarget)
open JTSupportedPathGraphData (GraphData)
open JTSupportedPathGraphEvaluation (reduced evaluation)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

variable {I : Type} [SmallCategory I] (W : Source) (z : Vertex W)
variable (L : I ⥤ DecoratedNecklaceHomDiagram.Index W z z)
variable (time S : I ⥤ SimplexCategory)
private abbrev K := JTParametrizedTargetFamilyComparison.degrees L
variable (u : S ⟶ K W z L)
variable (hs : ∀ a : I,
  std.map (u.app a) ≫ JTSupportedOrderedCoefficientChoices.old W z L a =
    JTSupportedOrderedCoefficientChoices.supportedConstant W z L S a)
variable (G : GraphData W z L time S u)
variable (hu : ∀ a : I, Mono (u.app a))

private def precomp_nullhomotopy {C D B : Type}
    [SmallCategory C] [SmallCategory D] [SmallCategory B]
    (p : D ⥤ B) (E : B ⥤ C) (v : (Δ[0] : SSet.{0}) ⟶ nerve C)
    (H : SSet.Homotopy (R.map (nerveMap E))
      (R.map (term (nerve B) ≫ v))) :
    SSet.Homotopy (R.map (nerveMap (p ⋙ E)))
      (R.map (term (nerve D) ≫ v)) := by
  have ht : nerveMap p ≫ term (nerve B) = term (nerve D) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  refine (H.precomp (R.map (nerveMap p))).congr ?_ ?_
  · rw [← R.map_comp]
    rfl
  · rw [← R.map_comp, ← Category.assoc, ht]

/-- Restrict the full label-contraction homotopy to either entire endpoint
presentation, keeping the original point-target comma and the same vertex. -/
theorem endpoint_nullhomotopic (b : Fin 2)
    (hG : ∀ a : I, trivialFibrations SSet.{0} (G.projection.app a)) :
    ∃ v : (Δ[0] : SSet.{0}) ⟶
        nerve (JTGraphFactoredPresentation.TargetComma (pointTarget W z)),
      Nonempty (SSet.Homotopy
        (R.map (nerveMap
          (JTSupportedPathEndpointPresentation.evaluation W z L time S u hs G hu b)))
        (R.map (term (nerve
          (JTSupportedPathEndpointPresentation.Presentation W z L time S u hs G b)) ≫ v))) := by
  obtain ⟨v, ⟨H⟩⟩ :=
    JTSupportedPathEvaluationNullhomotopy.evaluation_nullhomotopic
      W z L time S u hs G hu hG
  refine ⟨v, ?_⟩
  rw [JTSupportedPathEndpointPresentation.evaluation_eq_inclusion]
  exact ⟨precomp_nullhomotopy
    (JTSupportedPathEndpointPresentation.inclusion W z L time S u hs G b)
    (JTSupportedPathGraphEvaluation.evaluation W z L time S u hs G hu) v H⟩

/-- The full actual time-zero evaluation compares with the old evaluation
through the unchanged source-change functor on all internal necklaces. -/
def evaluationComparison :
    JTSupportedPathEndpointPresentation.evaluation W z L time S u hs G hu 0 ⟶
      JTSupportedPathZeroComparison.toOldPresentation W z L time S u hs G ⋙
        JTSupportedPathZeroComparison.oldEvaluation W z L time S u hs G := by
  rw [JTSupportedPathZeroComparison.oldEvaluation_eq_mapPresentation]
  exact JTBoundaryNecklaceTwoReindexComparison.comparison
    (JTTargetCommaPullback.diagram W z z (pointTarget W z))
    (reduced W z L time S u hs G)
    (JTSupportedPathGraphData.labels W z L S u hs)
    (JTSupportedPathGraphEvaluation.pullbackLift W z L time S u hs G hu)
    (JTSupportedPathChainEndpoints.endpointSection W z L S u hs 0)
    (JTSupportedPathZeroComparison.oldReduced W z L time S u G) L
    (JTSupportedPathZeroComparison.oldLift W z L time S u hs G)
    (JTSupportedPathChainEndpoints.endpointSection W z L S u hs 0 ⋙
      JTSupportedPathGraphData.base W z L S u hs)
    (JTSupportedPathZeroComparison.sourceChange W z L time S u hs G)
    (JTSupportedPathChainEndpoints.zeroToOld W z L S u hs)
    (JTSupportedPathZeroComparison.fixedTarget_square W z L time S u hs G hu)
    (JTTargetCommaExactEvaluation.fromPresentation W z z (pointTarget W z))

include hu in
/-- The original graph-covered supported-label evaluation itself is
nullhomotopic after singular realization, with its full original time. -/
theorem old_evaluation_nullhomotopic
    (hG : ∀ a : I, trivialFibrations SSet.{0} (G.projection.app a))
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hp : ∀ a : I, 0 < ((JTParametrizedTargetFamilies.codes L).obj a).len) :
    ∃ v : (Δ[0] : SSet.{0}) ⟶
        nerve (JTGraphFactoredPresentation.TargetComma (pointTarget W z)),
      Nonempty (SSet.Homotopy
        (R.map (nerveMap
          (JTSupportedPathZeroComparison.oldEvaluation W z L time S u hs G)))
        (R.map (term (nerve (BoundaryNecklaceComma.Presentation
          (JTSupportedPathZeroComparison.oldReduced W z L time S u G))) ≫ v))) := by
  obtain ⟨v, ⟨H⟩⟩ := endpoint_nullhomotopic W z L time S u hs G hu 0 hG
  let p := JTSupportedPathZeroComparison.toOldPresentation W z L time S u hs G
  let E := JTSupportedPathEndpointPresentation.evaluation W z L time S u hs G hu 0
  let F := JTSupportedPathZeroComparison.oldEvaluation W z L time S u hs G
  letI : WeakEquivalence (nerveMap p) :=
    JTSupportedPathZeroComparison.toOldPresentation_weak W z L time S u hs G hu hG hW hp
  have hz₀ : NatTransZigzag E (p ⋙ F) :=
    .rel _ _ ⟨evaluationComparison W z L time S u hs G hu⟩
  have hz : NatTransZigzag (p ⋙ F) E := hz₀.symm
  exact ⟨v, FiniteLastVertexSupport.nullhomotopic_of_weak_cover p F E hz v H⟩

end
end DaggerModels.PartII.JTSupportedPathOldNullhomotopy
