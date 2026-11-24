import DaggerModelsPartII.JTSupportedPathEndpointPresentation
import DaggerModelsPartII.JTPointTargetEvaluationCone
import DaggerModelsPartII.JTBoundaryNecklacePresentationTransport
import NativeOverNerveWeakContractibility

/-! Point cones on complete endpoint presentations of supported coefficient paths. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 100000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerOriginalProductGadget DaggerSSetGluing
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSupportedPathEndpointCone

open JTProjectiveOrderedFiberComparison (row)
open JTPointTargetEvaluationCone (pointTarget pointLabel center)
open JTSupportedPathGraphData (GraphData labels)
open JTSupportedPathGraphEvaluation (reduced pullbackLift)
open JTSupportedPathChainEndpoints (endpointSection)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev std := SSet.stdSimplex.{0}

private theorem factorOfCone {A : Type} [SmallCategory A]
    (W : Source) (z : Vertex W)
    (F : A ⥤ JTGraphFactoredPresentation.TargetComma (pointTarget W z))
    (c : NatTrans F ((Functor.const A).obj (center W z))) :
    ∃ (C : Cat.{0, 0}) (v : A ⥤ C)
      (w : C ⥤ JTGraphFactoredPresentation.TargetComma (pointTarget W z)),
      GW (pointMap (nerve C)) ∧ F = v ⋙ w := by
  refine ⟨Cat.of (Over (center W z)), Over.lift F c,
    Over.forget (center W z),
    DaggerNativeOverNerveWeakContractibility.point_GW _, rfl⟩

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

private abbrev endpointPresentation (b : Fin 2) :=
  JTSupportedPathEndpointPresentation.Presentation W z L time S u hs G b

private abbrev endpointEvaluation (b : Fin 2) :=
  Grothendieck.pre (BoundaryNecklaceComma.fiberDiagram
    (reduced W z L time S u hs G)) (endpointSection W z L S u hs b) ⋙
    (JTBoundaryNecklacePresentationCone.mapPresentation
      (JTTargetCommaPullback.diagram W z z (pointTarget W z))
      (reduced W z L time S u hs G) (labels W z L S u hs)
      (pullbackLift W z L time S u hs G hu) ⋙
      JTTargetCommaExactEvaluation.fromPresentation W z z (pointTarget W z))

/-- The explicit evaluation spelling is the actual complete endpoint evaluation. -/
private theorem endpointEvaluation_eq (b : Fin 2) :
    endpointEvaluation W z L time S u hs G hu b =
      JTSupportedPathEndpointPresentation.evaluation W z L time S u hs G hu b := rfl

private abbrev constantCenter (b : Fin 2) :=
  (Functor.const (endpointPresentation W z L time S u hs G b)).obj (center W z)

/-- A point cone on the decorated labels of a complete endpoint presentation
induces a cone on its unchanged native and time evaluation. -/
def endpoint_toPoint_ofLabelCone (b : Fin 2)
    (σ : NatTrans (endpointSection W z L S u hs b ⋙ labels W z L S u hs)
      ((Functor.const (JTSupportedPathChainLabels.First W z L S u hs)).obj
        (pointLabel W z))) :
    NatTrans (endpointEvaluation W z L time S u hs G hu b)
      (constantCenter W z L time S u hs G b) := by
  exact JTPointTargetEvaluationCone.evaluation_toPointAfterReindex W z
    (reduced W z L time S u hs G) (labels W z L S u hs)
    (pullbackLift W z L time S u hs G hu)
    (endpointSection W z L S u hs b) σ

/-- A point cone on one complete endpoint gives an exact factorization through
the weakly contractible slice over the same literal center. -/
theorem exists_contractible_factor_ofLabelCone (b : Fin 2)
    (σ : NatTrans (endpointSection W z L S u hs b ⋙ labels W z L S u hs)
      ((Functor.const (JTSupportedPathChainLabels.First W z L S u hs)).obj
        (pointLabel W z))) :
    ∃ (C : Cat.{0, 0})
      (v : endpointPresentation W z L time S u hs G b ⥤ C)
      (w : C ⥤ JTGraphFactoredPresentation.TargetComma (pointTarget W z)),
      GW (pointMap (nerve C)) ∧
        endpointEvaluation W z L time S u hs G hu b =
          v ⋙ w := by
  exact factorOfCone W z (endpointEvaluation W z L time S u hs G hu b)
    (endpoint_toPoint_ofLabelCone W z L time S u hs G hu b σ)

/-- The complete time-one endpoint evaluation contracts to the literal
point-target center. This includes every native necklace and original time. -/
def endpoint_toPoint :
    NatTrans (endpointEvaluation W z L time S u hs G hu 1)
      (constantCenter W z L time S u hs G 1) :=
  endpoint_toPoint_ofLabelCone W z L time S u hs G hu 1
    (JTSupportedPathChainEndpoints.oneToPoint W z L S u hs)

/-- The actual time-one evaluation factors exactly through the weakly
contractible slice over the fixed center. -/
theorem exists_contractible_factor :
    ∃ (C : Cat.{0, 0})
      (v : endpointPresentation W z L time S u hs G 1 ⥤ C)
      (w : C ⥤ JTGraphFactoredPresentation.TargetComma (pointTarget W z)),
      GW (pointMap (nerve C)) ∧
        endpointEvaluation W z L time S u hs G hu 1 =
          v ⋙ w :=
  exists_contractible_factor_ofLabelCone W z L time S u hs G hu 1
    (JTSupportedPathChainEndpoints.oneToPoint W z L S u hs)

end
end DaggerModels.PartII.JTSupportedPathEndpointCone
