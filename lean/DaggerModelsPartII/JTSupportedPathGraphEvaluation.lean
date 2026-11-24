import DaggerModelsPartII.JTSupportedPathGraphData

/-! Complete fixed-target evaluations of all supported higher contraction paths. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSupportedPathGraphEvaluation

open JTProjectiveOrderedFiberComparison (row)
open JTParametrizedTargetFamilies (codes)
open JTPointTargetEvaluationCone (pointTarget)
open JTSupportedPathGraphData (GraphData nativePrism Index base labels oldTime
  graph projection parameter supportParameter)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev J := GroupoidSimplex.parameter
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

private theorem nativePrism_map {a b : I} (f : a ⟶ b) :
    (nativePrism W z L time).map f =
      ((codes L).map f).map ⊗ₘ J.map (time.map f) :=
  JTDecoratedIntervalDiagram.parameterize_map_left (pointTarget W z).map J time
    (Over.lift (codes L) (JTOrderedLabelJointInsertion.toPointNatural (codes L)) ⋙
      JTTargetIntervalOverMapping.whole (pointTarget W z).code) f

/-- Recover the WHOLE unchanged native-time prism from all path-chain graph lifts. -/
def toPrism : graph W z L time S u hs G ⟶
    nativePrism W z (labels W z L S u hs) (oldTime W z L time S u hs) where
  app a := (projection W z L time S u hs G).app a ≫
    G.projection.app ((base W z L S u hs).obj a)
  naturality {a b} f := by
    have h := (projection W z L time S u hs G ≫
      Functor.whiskerLeft (base W z L S u hs) G.projection).naturality f
    change (graph W z L time S u hs G).map f ≫
        ((projection W z L time S u hs G).app b ≫ G.projection.app _) =
      ((projection W z L time S u hs G).app a ≫ G.projection.app _) ≫
        (nativePrism W z (labels W z L S u hs) (oldTime W z L time S u hs)).map f
    rw [nativePrism_map]
    change (graph W z L time S u hs G).map f ≫
        ((projection W z L time S u hs G).app b ≫ G.projection.app _) =
      ((projection W z L time S u hs G).app a ≫ G.projection.app _) ≫
        (nativePrism W z L time).map ((base W z L S u hs).map f) at h
    rw [nativePrism_map] at h
    simpa only [Category.assoc] using h

/-- The graph-to-full-prism comparison remains an actual trivial fibration. -/
theorem toPrism_trivialFibration
    (hG : ∀ a : I, trivialFibrations SSet.{0} (G.projection.app a))
    (a : Index W z L S u hs) :
    trivialFibrations SSet.{0} ((toPrism W z L time S u hs G).app a) :=
  (trivialFibrations SSet.{0}).comp_mem _ _
    (JTSupportedPathGraphData.projection_trivialFibration W z L time S u hs G a)
    (hG ((base W z L S u hs).obj a))

/-- Every path-chain label collapses to the literal same point native target. -/
abbrev collapse := JTOrderedLabelJointInsertion.toPointNatural
  (codes (labels W z L S u hs))

/-- Collapse the ENTIRE inverse image of the two endpoint lines, keeping all time. -/
abbrev reduced := JTGraphCoveredLabelEvaluation.reduced (pointTarget W z)
  (labels W z L S u hs) (oldTime W z L time S u hs) (collapse W z L S u hs)
  (toPrism W z L time S u hs G)

variable (hu : ∀ a : I, Mono (u.app a))

include hu in
/-- The literal full graph equation for the changing higher path-chain label. -/
theorem raw (a : Index W z L S u hs) :
    lift ((toPrism W z L time S u hs G).app a ≫
        fst ((codes (labels W z L S u hs)).obj a).toSSet
          (J.obj ((oldTime W z L time S u hs).obj a)))
        ((parameter W z L time S u hs G).app a) ≫
      JTNecklaceLabelRealization.realizedLabel
        ((codes (labels W z L S u hs)).obj a).toSSet W
        ((JTSupportedPathChainLabels.ordinals W z L S u hs).obj a)
        (JTRealizedLabelEndpoints.orderedLabel W z z
          ((codes (labels W z L S u hs)).obj a)
          ((JTSupportedPathChainLabels.ordinals W z L S u hs).obj a)
          (OrderedLabelElements.label W (OrderedNecklaceVertexPoints.boundaryPoint W z z)
            ((labels W z L S u hs).obj a))) =
      ((toPrism W z L time S u hs G).app a ≫
        fst ((codes (labels W z L S u hs)).obj a).toSSet
          (J.obj ((oldTime W z L time S u hs).obj a))) ≫
        ((collapse W z L S u hs).app a).map ≫ (pointTarget W z).map := by
  let a₀ := (base W z L S u hs).obj a
  let T := (codes L).obj a₀
  let d := (JTSupportedPathChainLabels.ordinals W z L S u hs).obj a
  letI := hu a₀
  have hθ := NatTrans.congr_app
    (JTSupportedPathGraphData.parameter_support W z L time S u hs G) a
  have hc := JTSupportedPathChainLabels.coefficientMap_raw W z L S u hs a
    ((toPrism W z L time S u hs G).app a ≫
      fst T.toSSet (J.obj ((oldTime W z L time S u hs).obj a)))
    ((parameter W z L time S u hs G).app a)
    ((supportParameter W z L time S u hs G).app a) hθ
  have hl : JTRealizedLabelEndpoints.orderedLabel W z z T d
      (OrderedLabelElements.label W (OrderedNecklaceVertexPoints.boundaryPoint W z z)
        ((labels W z L S u hs).obj a)) =
    SSet.yonedaEquiv (JTSupportedPathChainLabels.coefficientMap W z L S u hs a) := by
    rw [← JTSupportedPathChainLabels.labels_coefficient W z L S u hs a]
    exact (Equiv.apply_symm_apply SSet.yonedaEquiv _).symm
  change _ ≫ JTNecklaceLabelRealization.realizedLabel T.toSSet W d
    (JTRealizedLabelEndpoints.orderedLabel W z z T d _) = _
  rw [hl]
  have ht : (JTOrderedLabelJointInsertion.toPoint T).map = term T.toSSet :=
    JTOrderedLabelJointInsertion.pointIsTerminal.hom_ext _ _
  change _ = (((toPrism W z L time S u hs G).app a) ≫
    fst T.toSSet (J.obj ((oldTime W z L time S u hs).obj a))) ≫
      (JTOrderedLabelJointInsertion.toPoint T).map ≫ (pointTarget W z).map
  rw [ht]
  exact hc

include hu in
/-- The complete higher-label evaluation stays in the original fixed point-target comma. -/
def evaluation : BoundaryNecklaceComma.Presentation (reduced W z L time S u hs G) ⥤
    JTGraphFactoredPresentation.TargetComma (pointTarget W z) :=
  JTGraphCoveredLabelEvaluation.evaluation (pointTarget W z)
    (labels W z L S u hs) (oldTime W z L time S u hs) (collapse W z L S u hs)
    (toPrism W z L time S u hs G) (parameter W z L time S u hs G) (raw W z L time S u hs G hu)

include hu in
/-- The whole path graph lifts to the literal fixed-target pullback, retaining
both the complete decorated traversal and the native projection. -/
def pullbackLift : reduced W z L time S u hs G ⟶
    labels W z L S u hs ⋙ JTTargetCommaPullback.diagram W z z (pointTarget W z) :=
  JTDecoratedIntervalCylinder.liftFromProjections (pointTarget W z)
    (labels W z L S u hs) (reduced W z L time S u hs G)
    (JTGraphCoveredLabelEvaluation.decorated (pointTarget W z)
      (labels W z L S u hs) (oldTime W z L time S u hs) (collapse W z L S u hs)
      (toPrism W z L time S u hs G) (parameter W z L time S u hs G))
    (JTGraphCoveredLabelEvaluation.nativeLeg (pointTarget W z)
      (labels W z L S u hs) (oldTime W z L time S u hs) (collapse W z L S u hs)
      (toPrism W z L time S u hs G))
    (JTGraphCoveredLabelEvaluation.raw_square (pointTarget W z)
      (labels W z L S u hs) (oldTime W z L time S u hs) (collapse W z L S u hs)
      (toPrism W z L time S u hs G) (parameter W z L time S u hs G)
      (raw W z L time S u hs G hu))

/-- The evaluation is exactly the full fixed-target pullback presentation map. -/
theorem evaluation_eq_mapPresentation :
    evaluation W z L time S u hs G hu =
      JTBoundaryNecklacePresentationCone.mapPresentation
        (JTTargetCommaPullback.diagram W z z (pointTarget W z))
        (reduced W z L time S u hs G) (labels W z L S u hs)
        (pullbackLift W z L time S u hs G hu) ⋙
        JTTargetCommaExactEvaluation.fromPresentation W z z (pointTarget W z) := rfl

/-- The complete path-graph presentation retains the original diagram index. -/
abbrev toOriginal : BoundaryNecklaceComma.Presentation
    (reduced W z L time S u hs G) ⥤ I :=
  Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram
    (reduced W z L time S u hs G)) ⋙ base W z L S u hs

include hu in
/-- Full inverse-image presentation and all path/chain choices form a weak cover of I. -/
theorem toOriginal_weak
    (hG : ∀ a : I, trivialFibrations SSet.{0} (G.projection.app a))
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hp : ∀ a : I, 0 < ((codes L).obj a).len) :
    WeakEquivalence (nerveMap (toOriginal W z L time S u hs G)) := by
  haveI : WeakEquivalence (nerveMap (Grothendieck.forget
      (BoundaryNecklaceComma.fiberDiagram (reduced W z L time S u hs G)))) :=
    JTGraphCoveredPresentationWeak.forget_weak (pointTarget W z)
      (labels W z L S u hs) (oldTime W z L time S u hs) (collapse W z L S u hs)
      (toPrism W z L time S u hs G)
      (toPrism_trivialFibration W z L time S u hs G hG)
  haveI := JTSupportedPathChainLabels.toOriginal_weak W z L S u hs hu hW hp
  change WeakEquivalence (nerveMap (Grothendieck.forget
    (BoundaryNecklaceComma.fiberDiagram (reduced W z L time S u hs G))) ≫
      nerveMap (base W z L S u hs))
  infer_instance

end
end DaggerModels.PartII.JTSupportedPathGraphEvaluation
