import DaggerModelsPartII.JTSupportedPathGraphEvaluation
import DaggerModelsPartII.JTSupportedPathChainEndpoints
import DaggerModelsPartII.GrothendieckContractiblePreWeak

/-! Both time-face presentations inside the complete supported label-prism evaluation. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSupportedPathEndpointPresentation

open JTProjectiveOrderedFiberComparison (row)
open JTParametrizedTargetFamilies (codes)
open JTSupportedPathGraphData (GraphData labels oldTime)
open JTSupportedPathGraphEvaluation (reduced toPrism collapse)
open JTSupportedPathChainEndpoints (endpointSection)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev std := SSet.stdSimplex.{0}

variable {I : Type} [SmallCategory I] (W : Source) (z : Vertex W)
variable (L : I ⥤ DecoratedNecklaceHomDiagram.Index W z z)
variable (time S : I ⥤ SimplexCategory)
private abbrev K := JTParametrizedTargetFamilyComparison.degrees L
variable (u : S ⟶ K W z L)
variable (hs : ∀ a : I,
  std.map (u.app a) ≫ JTSupportedOrderedCoefficientChoices.old W z L a =
    JTSupportedOrderedCoefficientChoices.supportedConstant W z L S a)
variable (G : GraphData W z L time S u)

/-- The entire reduced-cylinder diagram restricted to one contraction time face. -/
abbrev endpointDiagram (b : Fin 2) :=
  endpointSection W z L S u hs b ⋙ reduced W z L time S u hs G

/-- All internal necklaces over the chosen endpoint, with its full original time. -/
abbrev Presentation (b : Fin 2) :=
  BoundaryNecklaceComma.Presentation (endpointDiagram W z L time S u hs G b)

/-- Insert the endpoint presentation into the complete higher label-prism presentation. -/
abbrev inclusion (b : Fin 2) : Presentation W z L time S u hs G b ⥤
    BoundaryNecklaceComma.Presentation (reduced W z L time S u hs G) :=
  Grothendieck.pre (BoundaryNecklaceComma.fiberDiagram
    (reduced W z L time S u hs G)) (endpointSection W z L S u hs b)

/-- Both endpoint inclusions are weak, retaining every internal-necklace fiber. -/
theorem inclusion_weak (b : Fin 2)
    (hG : ∀ a : I, trivialFibrations SSet.{0} (G.projection.app a)) :
    WeakEquivalence (nerveMap (inclusion W z L time S u hs G b)) := by
  apply GrothendieckContractiblePreWeak.pre_weak
  · intro a
    exact JTGraphCoveredPresentationWeak.fiber_point_GW
      (JTPointTargetEvaluationCone.pointTarget W z)
      (labels W z L S u hs) (oldTime W z L time S u hs)
      (collapse W z L S u hs) (toPrism W z L time S u hs G)
      (JTSupportedPathGraphEvaluation.toPrism_trivialFibration
        W z L time S u hs G hG) a
  · exact JTSupportedPathChainEndpoints.endpointSection_weak W z L S u hs b

variable (hu : ∀ a : I, Mono (u.app a))

/-- Evaluate the complete chosen time face in the same unchanged point-target comma. -/
def evaluation (b : Fin 2) :
    Presentation W z L time S u hs G b ⥤
      JTGraphFactoredPresentation.TargetComma (JTPointTargetEvaluationCone.pointTarget W z) :=
  inclusion W z L time S u hs G b ⋙
    (JTBoundaryNecklacePresentationCone.mapPresentation
      (JTTargetCommaPullback.diagram W z z (JTPointTargetEvaluationCone.pointTarget W z))
      (reduced W z L time S u hs G) (labels W z L S u hs)
      (JTSupportedPathGraphEvaluation.pullbackLift W z L time S u hs G hu) ⋙
      JTTargetCommaExactEvaluation.fromPresentation W z z
        (JTPointTargetEvaluationCone.pointTarget W z))

/-- The endpoint evaluation is exactly the whole path evaluation restricted
along its full presentation inclusion. -/
theorem evaluation_eq_inclusion (b : Fin 2) :
    evaluation W z L time S u hs G hu b =
      inclusion W z L time S u hs G b ⋙
        JTSupportedPathGraphEvaluation.evaluation W z L time S u hs G hu := rfl

/-- The endpoint comparison retains the original diagram index. -/
abbrev toOriginal (b : Fin 2) : Presentation W z L time S u hs G b ⥤ I :=
  inclusion W z L time S u hs G b ⋙
    JTSupportedPathGraphEvaluation.toOriginal W z L time S u hs G

include hu in
/-- Every complete time-face presentation weakly covers the original index. -/
theorem toOriginal_weak (b : Fin 2)
    (hG : ∀ a : I, trivialFibrations SSet.{0} (G.projection.app a))
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hp : ∀ a : I, 0 < ((codes L).obj a).len) :
    WeakEquivalence (nerveMap (toOriginal W z L time S u hs G b)) := by
  haveI := inclusion_weak W z L time S u hs G b hG
  haveI := JTSupportedPathGraphEvaluation.toOriginal_weak W z L time S u hs G hu hG hW hp
  change WeakEquivalence (nerveMap (inclusion W z L time S u hs G b) ≫
    nerveMap (JTSupportedPathGraphEvaluation.toOriginal W z L time S u hs G))
  infer_instance

end
end DaggerModels.PartII.JTSupportedPathEndpointPresentation
