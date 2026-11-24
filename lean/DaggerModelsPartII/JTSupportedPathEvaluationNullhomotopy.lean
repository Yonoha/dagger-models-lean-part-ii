import DaggerModelsPartII.JTSupportedPathEndpointCone
import DaggerModelsPartII.FiniteLastVertexFactor

/-! A complete supported label-prism evaluation contracts after singular realization. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerNerveHomotopy
open DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSupportedPathEvaluationNullhomotopy

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

/-- The entire higher-path graph evaluation is nullhomotopic after singular
realization, using its actual weak final-time presentation and point cone.
This does not assert a factor of every intermediate label through the point. -/
theorem evaluation_nullhomotopic
    (hG : ∀ a : I, trivialFibrations SSet.{0} (G.projection.app a)) :
    ∃ v : (Δ[0] : SSet.{0}) ⟶
        nerve (JTGraphFactoredPresentation.TargetComma (pointTarget W z)),
      Nonempty (SSet.Homotopy
        (R.map (nerveMap (evaluation W z L time S u hs G hu)))
        (R.map (term (nerve (BoundaryNecklaceComma.Presentation
          (reduced W z L time S u hs G))) ≫ v))) := by
  haveI := JTSupportedPathEndpointPresentation.inclusion_weak W z L time S u hs G 1 hG
  obtain ⟨E, F, H, hE, hfactor⟩ :=
    JTSupportedPathEndpointCone.exists_contractible_factor W z L time S u hs G hu
  apply FiniteLastVertexFactor.nerveMap_nullhomotopic_of_weak_cover
    (JTSupportedPathEndpointPresentation.inclusion W z L time S u hs G 1)
    (evaluation W z L time S u hs G hu) F H hE
  have hfac : JTSupportedPathEndpointPresentation.inclusion W z L time S u hs G 1 ⋙
      evaluation W z L time S u hs G hu = F ⋙ H :=
    (JTSupportedPathEndpointPresentation.evaluation_eq_inclusion
      W z L time S u hs G hu 1).symm.trans hfactor
  exact .rel _ _ ⟨eqToHom hfac⟩

end
end DaggerModels.PartII.JTSupportedPathEvaluationNullhomotopy
