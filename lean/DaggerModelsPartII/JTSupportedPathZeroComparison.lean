import DaggerModelsPartII.JTSupportedPathEndpointPresentation
import DaggerModelsPartII.JTBoundaryNecklacePresentationTimeChange
import DaggerModelsPartII.JTSupportedPathZeroTransport

/-! The full time-zero supported path retains the original graph and coefficient. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSupportedPathZeroComparison

open JTProjectiveOrderedFiberComparison (row)
open JTParametrizedTargetFamilies (codes)
open JTSupportedPathGraphData (GraphData)
open JTPointTargetEvaluationCone (pointTarget)
open DecoratedCylinderNecklacePresentation (underDiagram underCocone)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev std := SSet.stdSimplex.{0}
private abbrev J := GroupoidSimplex.parameter
private abbrev B := JTXiEndpointCollapse.boundary
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {I : Type} [SmallCategory I] (W : Source) (z : Vertex W)
variable (L : I ⥤ DecoratedNecklaceHomDiagram.Index W z z)
variable (time S : I ⥤ SimplexCategory)
private abbrev K := JTParametrizedTargetFamilyComparison.degrees L
variable (u : S ⟶ K W z L)
variable (hs : ∀ a : I,
  std.map (u.app a) ≫ JTSupportedOrderedCoefficientChoices.old W z L a =
    JTSupportedOrderedCoefficientChoices.supportedConstant W z L S a)
variable (G : GraphData W z L time S u)

private abbrev collapse := JTOrderedLabelJointInsertion.toPointNatural (codes L)

/-- The original graph covered reduced cylinder, before taking any path choice. -/
abbrev oldReduced := JTGraphCoveredLabelEvaluation.reduced (pointTarget W z)
  L time (collapse W z L) G.projection

include hs in
/-- The original graph coefficient already has the point raw value on its
entire supported graph, including the unchanged full time simplex. -/
theorem oldRaw (a : I) :
    lift (G.projection.app a ≫
        fst ((codes L).obj a).toSSet (J.obj (time.obj a)))
        (G.parameter.app a) ≫
      JTNecklaceLabelRealization.realizedLabel ((codes L).obj a).toSSet W
        ((K W z L).obj a)
        (JTRealizedLabelEndpoints.orderedLabel W z z
          ((codes L).obj a) ((K W z L).obj a)
          (OrderedLabelElements.label W
            (OrderedNecklaceVertexPoints.boundaryPoint W z z) (L.obj a))) =
    (G.projection.app a ≫
        fst ((codes L).obj a).toSSet (J.obj (time.obj a))) ≫
      ((collapse W z L).app a).map ≫ (pointTarget W z).map := by
  let T := (codes L).obj a
  let h := G.projection.app a ≫ fst T.toSSet (J.obj (time.obj a))
  have hθ : G.parameter.app a = G.supportParameter.app a ≫ J.map (u.app a) := by
    exact (NatTrans.congr_app G.support_fac a).symm
  have hc : JTRealizedLabelEndpoints.orderedLabel W z z T ((K W z L).obj a)
      (OrderedLabelElements.label W
        (OrderedNecklaceVertexPoints.boundaryPoint W z z) (L.obj a)) =
      SSet.yonedaEquiv (JTSupportedOrderedCoefficientChoices.old W z L a) := by
    exact (Equiv.apply_symm_apply SSet.yonedaEquiv _).symm
  rw [hθ, hc]
  change lift h (G.supportParameter.app a ≫ J.map (u.app a)) ≫
      JTNecklaceLabelRealization.realizedLabel T.toSSet W ((K W z L).obj a)
        (SSet.yonedaEquiv (JTSupportedOrderedCoefficientChoices.old W z L a)) = _
  rw [JTWhiskerEdgeGraphRaw.coefficient_reindex]
  rw [hs a]
  change lift h (G.supportParameter.app a) ≫
    JTNecklaceLabelRealization.realizedLabel T.toSSet W (S.obj a)
      (SSet.yonedaEquiv
        (JTConstantOrderedLabel.constantCoefficient W z T (S.obj a))) = _
  have hr := JTComposedPrismLabels.rawProduct_constant W z T
    (snd T.toSSet (J.obj (S.obj a)))
  dsimp only [JTComposedPrismLabels.rawProduct,
    JTBinaryPrismRealization.realizeProduct] at hr
  rw [lift_fst_snd, Category.id_comp] at hr
  rw [hr]
  have hf : lift h (G.supportParameter.app a) ≫
      fst T.toSSet (J.obj (S.obj a)) = h := lift_fst _ _
  simp only [← Category.assoc, hf]
  have ht : ((collapse W z L).app a).map = term T.toSSet :=
    JTOrderedLabelJointInsertion.pointIsTerminal.hom_ext _ _
  rw [ht]
  change (h ≫ term T.toSSet) ≫ SSet.yonedaEquiv.symm (rawVertex W z) =
    (h ≫ term T.toSSet) ≫ SSet.yonedaEquiv.symm (rawVertex W z)
  rfl

/-- Evaluation of the unchanged graph and old normalized labels in the
literal point-target comma. -/
def oldEvaluation : BoundaryNecklaceComma.Presentation (oldReduced W z L time S u G) ⥤
    JTGraphFactoredPresentation.TargetComma (pointTarget W z) :=
  JTGraphCoveredLabelEvaluation.evaluation (pointTarget W z) L time
    (collapse W z L) G.projection G.parameter (oldRaw W z L time S u hs G)

/-- The old graph-covered reduction keeps both maps into the fixed target pullback. -/
def oldLift : oldReduced W z L time S u G ⟶
    L ⋙ JTTargetCommaPullback.diagram W z z (pointTarget W z) :=
  JTDecoratedIntervalCylinder.liftFromProjections (pointTarget W z)
    L (oldReduced W z L time S u G)
    (JTGraphCoveredLabelEvaluation.decorated (pointTarget W z)
      L time (collapse W z L) G.projection G.parameter)
    (JTGraphCoveredLabelEvaluation.nativeLeg (pointTarget W z)
      L time (collapse W z L) G.projection)
    (JTGraphCoveredLabelEvaluation.raw_square (pointTarget W z)
      L time (collapse W z L) G.projection G.parameter
      (oldRaw W z L time S u hs G))

theorem oldEvaluation_eq_mapPresentation :
    oldEvaluation W z L time S u hs G =
      JTBoundaryNecklacePresentationCone.mapPresentation
        (JTTargetCommaPullback.diagram W z z (pointTarget W z))
        (oldReduced W z L time S u G) L
        (oldLift W z L time S u hs G) ⋙
          JTTargetCommaExactEvaluation.fromPresentation W z z (pointTarget W z) := rfl

private abbrev First := JTSupportedPathChainLabels.First W z L S u hs
private abbrev zeroSection : First W z L S u hs ⥤
    JTSupportedPathChainLabels.Index W z L S u hs :=
  JTSupportedPathChainEndpoints.endpointSection W z L S u hs 0
private abbrev original : First W z L S u hs ⥤ I :=
  zeroSection W z L S u hs ⋙ JTSupportedPathGraphData.base W z L S u hs

private abbrev newGraph :=
  zeroSection W z L S u hs ⋙ JTSupportedPathGraphData.graph W z L time S u hs G
private abbrev graphToOld : newGraph W z L time S u hs G ⟶
    original W z L S u hs ⋙ G.domain :=
  Functor.whiskerLeft (zeroSection W z L S u hs)
    (JTSupportedPathGraphData.projection W z L time S u hs G)

private abbrev oldProduct :=
  original W z L S u hs ⋙ JTSupportedPathGraphData.nativePrism W z L time
private abbrev oldProjection : original W z L S u hs ⋙ G.domain ⟶
    oldProduct W z L time S u hs :=
  Functor.whiskerLeft (original W z L S u hs) G.projection
private abbrev newProjection : newGraph W z L time S u hs G ⟶
    oldProduct W z L time S u hs :=
  graphToOld W z L time S u hs G ≫ oldProjection W z L time S u hs G

private theorem newProjection_eq :
    newProjection W z L time S u hs G =
      Functor.whiskerLeft (zeroSection W z L S u hs)
        (JTSupportedPathGraphEvaluation.toPrism W z L time S u hs G) := by
  apply NatTrans.ext
  funext a
  rfl

private abbrev oldBoundary :
    (original W z L S u hs ⋙ time ⋙ JTXiEndpointCollapse.boundaryCylinder) ⟶
      oldProduct W z L time S u hs :=
  Functor.whiskerLeft (original W z L S u hs)
    (JTGraphCoveredLabelEvaluation.boundary (pointTarget W z)
      L time (collapse W z L))

private def oldEndpointCollapse :
    (original W z L S u hs ⋙ time ⋙ JTXiEndpointCollapse.boundaryCylinder) ⟶
      (Functor.const (First W z L S u hs)).obj JTXiEndpointCollapse.boundary :=
  Functor.whiskerLeft (original W z L S u hs)
    (Functor.whiskerLeft time JTXiEndpointCollapse.cylinderProjection)

private def newBoundary :
    JTSupportedPathGraphData.oldTime W z L time S u hs ⋙
      JTXiEndpointCollapse.boundaryCylinder ⟶
    JTSupportedPathGraphData.nativePrism W z
      (JTSupportedPathGraphData.labels W z L S u hs)
      (JTSupportedPathGraphData.oldTime W z L time S u hs) :=
  JTGraphCoveredLabelEvaluation.boundary (pointTarget W z)
  (JTSupportedPathGraphData.labels W z L S u hs)
  (JTSupportedPathGraphData.oldTime W z L time S u hs)
  (JTSupportedPathGraphEvaluation.collapse W z L S u hs)

private theorem boundary_reindex (p : First W z L S u hs) :
    (newBoundary W z L time S u hs).app ((zeroSection W z L S u hs).obj p) =
      (oldBoundary W z L time S u hs).app p := rfl

private theorem graph_square (p : First W z L S u hs) :
    (JTSupportedPathGraphEvaluation.toPrism W z L time S u hs G).app
        ((zeroSection W z L S u hs).obj p) =
      (graphToOld W z L time S u hs G).app p ≫ G.projection.app
        ((original W z L S u hs).obj p) := rfl


private abbrev newCover : First W z L S u hs ⥤ SSet.{0} :=
  zeroSection W z L S u hs ⋙
  JTEndpointReducedPullbackCover.covered
    (JTSupportedPathGraphEvaluation.toPrism W z L time S u hs G)
    (newBoundary W z L time S u hs)

private def oldCover : First W z L S u hs ⥤ SSet.{0} :=
  original W z L S u hs ⋙
  JTEndpointReducedPullbackCover.covered G.projection
    (JTGraphCoveredLabelEvaluation.boundary (pointTarget W z)
      L time (collapse W z L))


private def newU : newCover W z L time S u hs G ⟶
    newGraph W z L time S u hs G :=
  Functor.whiskerLeft (zeroSection W z L S u hs)
    (pullback.fst (JTSupportedPathGraphEvaluation.toPrism W z L time S u hs G)
      (newBoundary W z L time S u hs))

private def newV : newCover W z L time S u hs G ⟶
    zeroSection W z L S u hs ⋙
      (JTSupportedPathGraphData.oldTime W z L time S u hs ⋙
        JTXiEndpointCollapse.boundaryCylinder) :=
  Functor.whiskerLeft (zeroSection W z L S u hs)
    (pullback.snd (JTSupportedPathGraphEvaluation.toPrism W z L time S u hs G)
      (newBoundary W z L time S u hs))


private def coverQ : newCover W z L time S u hs G ⟶
    original W z L S u hs ⋙ G.domain :=
  newU W z L time S u hs G ≫ graphToOld W z L time S u hs G

private def coverV : newCover W z L time S u hs G ⟶
    original W z L S u hs ⋙ time ⋙ JTXiEndpointCollapse.boundaryCylinder :=
  newV W z L time S u hs G

private theorem cover_square :
    coverQ W z L time S u hs G ≫
      Functor.whiskerLeft (original W z L S u hs) G.projection =
    coverV W z L time S u hs G ≫
      Functor.whiskerLeft (original W z L S u hs)
        (JTGraphCoveredLabelEvaluation.boundary (pointTarget W z)
          L time (collapse W z L)) := by
  apply NatTrans.ext
  funext p
  have hnew := NatTrans.congr_app
    (pullback.condition
      (f := JTSupportedPathGraphEvaluation.toPrism W z L time S u hs G)
      (g := newBoundary W z L time S u hs))
    ((zeroSection W z L S u hs).obj p)
  change (newU W z L time S u hs G).app p ≫
      (JTSupportedPathGraphEvaluation.toPrism W z L time S u hs G).app
        ((zeroSection W z L S u hs).obj p) =
    (newV W z L time S u hs G).app p ≫
      (newBoundary W z L time S u hs).app
        ((zeroSection W z L S u hs).obj p) at hnew
  rw [graph_square, boundary_reindex] at hnew
  change ((newU W z L time S u hs G).app p ≫
      (graphToOld W z L time S u hs G).app p) ≫
        G.projection.app ((original W z L S u hs).obj p) =
    (newV W z L time S u hs G).app p ≫
      (oldBoundary W z L time S u hs).app p
  rw [Category.assoc]
  exact hnew

/-- The entire covered boundary maps to the original covered boundary,
retaining its old graph point and endpoint coordinate. -/
def coverMap : newCover W z L time S u hs G ⟶ oldCover W z L time S u hs G :=
  JTSupportedPathZeroTransport.lift (original W z L S u hs)
    G.projection
    (JTGraphCoveredLabelEvaluation.boundary (pointTarget W z)
      L time (collapse W z L))
    (coverQ W z L time S u hs G) (coverV W z L time S u hs G)
    (cover_square W z L time S u hs G)

private def newE : newCover W z L time S u hs G ⟶
    (Functor.const (First W z L S u hs)).obj JTXiEndpointCollapse.boundary :=
  newV W z L time S u hs G ≫ oldEndpointCollapse W z L time S u hs

private abbrev oldU₀ := JTEndpointReducedPullbackCover.boundaryInclusion
  G.projection
  (JTGraphCoveredLabelEvaluation.boundary (pointTarget W z)
    L time (collapse W z L))
private abbrev oldE₀ := JTEndpointReducedPullbackCover.collapse
  G.projection
  (JTGraphCoveredLabelEvaluation.boundary (pointTarget W z)
    L time (collapse W z L))
  (Functor.whiskerLeft time JTXiEndpointCollapse.cylinderProjection)

private def oldInl : original W z L S u hs ⋙ G.domain ⟶
    (original W z L S u hs ⋙ oldReduced W z L time S u G) ⋙
      Under.forget JTXiEndpointCollapse.boundary :=
  Functor.whiskerLeft (original W z L S u hs)
    (pushout.inl (oldU₀ W z L time S u G) (oldE₀ W z L time S u G))

private def oldInr :
    (Functor.const (First W z L S u hs)).obj JTXiEndpointCollapse.boundary ⟶
    (original W z L S u hs ⋙ oldReduced W z L time S u G) ⋙
      Under.forget JTXiEndpointCollapse.boundary :=
  Functor.whiskerLeft (original W z L S u hs)
    (pushout.inr (oldU₀ W z L time S u G) (oldE₀ W z L time S u G))

private abbrev newU₀ := JTEndpointReducedPullbackCover.boundaryInclusion
  (JTSupportedPathGraphEvaluation.toPrism W z L time S u hs G)
  (newBoundary W z L time S u hs)
private abbrev newE₀ := JTEndpointReducedPullbackCover.collapse
  (JTSupportedPathGraphEvaluation.toPrism W z L time S u hs G)
  (newBoundary W z L time S u hs)
  (Functor.whiskerLeft (JTSupportedPathGraphData.oldTime W z L time S u hs)
    JTXiEndpointCollapse.cylinderProjection)

private def newInl : newGraph W z L time S u hs G ⟶
    JTSupportedPathEndpointPresentation.endpointDiagram W z L time S u hs G 0 ⋙
      Under.forget JTXiEndpointCollapse.boundary :=
  Functor.whiskerLeft (zeroSection W z L S u hs)
    (pushout.inl (newU₀ W z L time S u hs G) (newE₀ W z L time S u hs G))

private def newInr :
    (Functor.const (First W z L S u hs)).obj JTXiEndpointCollapse.boundary ⟶
    JTSupportedPathEndpointPresentation.endpointDiagram W z L time S u hs G 0 ⋙
      Under.forget JTXiEndpointCollapse.boundary :=
  Functor.whiskerLeft (zeroSection W z L S u hs)
    (pushout.inr (newU₀ W z L time S u hs G) (newE₀ W z L time S u hs G))

private def oldU := Functor.whiskerLeft (original W z L S u hs)
  (oldU₀ W z L time S u G)
private def oldE := Functor.whiskerLeft (original W z L S u hs)
  (oldE₀ W z L time S u G)

private theorem coverMap_u :
    newU W z L time S u hs G ≫ graphToOld W z L time S u hs G =
      coverMap W z L time S u hs G ≫ oldU W z L time S u hs G := by
  exact (JTSupportedPathZeroTransport.lift_fst
    (original W z L S u hs) G.projection
    (JTGraphCoveredLabelEvaluation.boundary (pointTarget W z)
      L time (collapse W z L))
    (coverQ W z L time S u hs G) (coverV W z L time S u hs G)
    (cover_square W z L time S u hs G)).symm

private theorem coverMap_e :
    newE W z L time S u hs G =
      coverMap W z L time S u hs G ≫ oldE W z L time S u hs G := by
  have hv := (JTSupportedPathZeroTransport.lift_snd
    (original W z L S u hs) G.projection
    (JTGraphCoveredLabelEvaluation.boundary (pointTarget W z)
      L time (collapse W z L))
    (coverQ W z L time S u hs G) (coverV W z L time S u hs G)
    (cover_square W z L time S u hs G)).symm
  have hvc := congrArg (· ≫ oldEndpointCollapse W z L time S u hs) hv
  simpa only [newE, oldE, oldE₀, JTEndpointReducedPullbackCover.collapse,
    Functor.whiskerLeft_comp, Category.assoc] using hvc

private theorem oldCocone :
    oldU W z L time S u hs G ≫ oldInl W z L time S u hs G =
      oldE W z L time S u hs G ≫ oldInr W z L time S u hs G := by
  have h := congrArg (Functor.whiskerLeft (original W z L S u hs))
    (pushout.condition (f := oldU₀ W z L time S u G)
      (g := oldE₀ W z L time S u G))
  simpa only [oldU, oldE, oldInl, oldInr,
    Functor.whiskerLeft_comp] using h

private theorem sourceCocone :
    newU W z L time S u hs G ≫
      (graphToOld W z L time S u hs G ≫ oldInl W z L time S u hs G) =
    newE W z L time S u hs G ≫ oldInr W z L time S u hs G := by
  calc
    _ = (newU W z L time S u hs G ≫
        graphToOld W z L time S u hs G) ≫
          oldInl W z L time S u hs G := (Category.assoc _ _ _).symm
    _ = (coverMap W z L time S u hs G ≫
        oldU W z L time S u hs G) ≫ oldInl W z L time S u hs G :=
      congrArg (· ≫ oldInl W z L time S u hs G)
        (coverMap_u W z L time S u hs G)
    _ = coverMap W z L time S u hs G ≫
        (oldU W z L time S u hs G ≫ oldInl W z L time S u hs G) :=
      Category.assoc _ _ _
    _ = coverMap W z L time S u hs G ≫
        (oldE W z L time S u hs G ≫ oldInr W z L time S u hs G) :=
      congrArg (coverMap W z L time S u hs G ≫ ·)
        (oldCocone W z L time S u hs G)
    _ = (coverMap W z L time S u hs G ≫ oldE W z L time S u hs G) ≫
        oldInr W z L time S u hs G := (Category.assoc _ _ _).symm
    _ = _ := congrArg (· ≫ oldInr W z L time S u hs G)
      (coverMap_e W z L time S u hs G).symm

private theorem endpointPushout (p : First W z L S u hs) :
    IsPushout ((newU W z L time S u hs G).app p)
      ((newE W z L time S u hs G).app p)
      ((newInl W z L time S u hs G).app p)
      ((newInr W z L time S u hs G).app p) := by
  exact (IsPushout.of_hasPushout
    (newU₀ W z L time S u hs G)
    (newE₀ W z L time S u hs G)).map
      ((CategoryTheory.evaluation
        (JTSupportedPathChainLabels.Index W z L S u hs) SSet.{0}).obj
          ((zeroSection W z L S u hs).obj p))

/-- The whole time-zero inverse-image quotient maps to the old quotient,
including every graph simplex and every collapsed endpoint simplex. -/
def sourceUnderlying :
    JTSupportedPathEndpointPresentation.endpointDiagram W z L time S u hs G 0 ⋙
      Under.forget JTXiEndpointCollapse.boundary ⟶
    (original W z L S u hs ⋙ oldReduced W z L time S u G) ⋙
      Under.forget JTXiEndpointCollapse.boundary :=
  JTSupportedPathZeroTransport.pushoutDesc
    (newU W z L time S u hs G) (newE W z L time S u hs G)
    (newInl W z L time S u hs G) (newInr W z L time S u hs G)
    (endpointPushout W z L time S u hs G)
    (graphToOld W z L time S u hs G ≫ oldInl W z L time S u hs G)
    (oldInr W z L time S u hs G)
    (sourceCocone W z L time S u hs G)

/-- Exact source change of complete reduced cylinders under the same
ordered endpoint boundary. -/
def sourceChange :
    JTSupportedPathEndpointPresentation.endpointDiagram W z L time S u hs G 0 ⟶
      original W z L S u hs ⋙ oldReduced W z L time S u G where
  app p := Under.homMk ((sourceUnderlying W z L time S u hs G).app p) (by
    have h := NatTrans.congr_app
      (JTSupportedPathZeroTransport.pushoutDesc_inr
        (newU W z L time S u hs G) (newE W z L time S u hs G)
        (newInl W z L time S u hs G) (newInr W z L time S u hs G)
        (endpointPushout W z L time S u hs G)
        (graphToOld W z L time S u hs G ≫ oldInl W z L time S u hs G)
        (oldInr W z L time S u hs G)
        (sourceCocone W z L time S u hs G)) p
    exact h)
  naturality {p q} f :=
    Under.UnderMorphism.ext ((sourceUnderlying W z L time S u hs G).naturality f)

theorem sourceChange_cylinder (p : First W z L S u hs) :
    (newInl W z L time S u hs G).app p ≫
      ((sourceChange W z L time S u hs G).app p).right =
    (graphToOld W z L time S u hs G).app p ≫
      (oldInl W z L time S u hs G).app p :=
  NatTrans.congr_app
    (JTSupportedPathZeroTransport.pushoutDesc_inl
      (newU W z L time S u hs G) (newE W z L time S u hs G)
      (newInl W z L time S u hs G) (newInr W z L time S u hs G)
      (endpointPushout W z L time S u hs G)
      (graphToOld W z L time S u hs G ≫ oldInl W z L time S u hs G)
      (oldInr W z L time S u hs G)
      (sourceCocone W z L time S u hs G)) p

theorem sourceChange_boundary (p : First W z L S u hs) :
    (newInr W z L time S u hs G).app p ≫
      ((sourceChange W z L time S u hs G).app p).right =
    (oldInr W z L time S u hs G).app p :=
  NatTrans.congr_app
    (JTSupportedPathZeroTransport.pushoutDesc_inr
      (newU W z L time S u hs G) (newE W z L time S u hs G)
      (newInl W z L time S u hs G) (newInr W z L time S u hs G)
      (endpointPushout W z L time S u hs G)
      (graphToOld W z L time S u hs G ≫ oldInl W z L time S u hs G)
      (oldInr W z L time S u hs G)
      (sourceCocone W z L time S u hs G)) p

/-- The graph coordinate at time zero is the complete original coefficient
parameter after the endpoint ordinal, on every graph simplex. -/
theorem zeroParameter_projection (p : First W z L S u hs) :
    (JTSupportedPathGraphData.parameter W z L time S u hs G).app
        ((zeroSection W z L S u hs).obj p) ≫
      J.map ((JTSupportedPathChainEndpoints.endpointDegree W z L S u hs 0).app p) =
    (graphToOld W z L time S u hs G).app p ≫
      G.parameter.app ((original W z L S u hs).obj p) := by
  let X : JTSupportedPathChainLabels.Index W z L S u hs ⥤ SSet.{0} :=
    JTSupportedPathGraphData.base W z L S u hs ⋙ G.domain
  let p₀ : X ⟶
      (JTSupportedPathGraphData.base W z L S u hs ⋙ K W z L) ⋙ J :=
    Functor.whiskerLeft (JTSupportedPathGraphData.base W z L S u hs) G.parameter
  let α₀ := JTSupportedPathChainLabels.toOldCoefficient W z L S u hs
  have h := JTPrismChainGraphCover.parameter_projection X p₀ α₀
  have hp := NatTrans.congr_app h ((zeroSection W z L S u hs).obj p)
  exact hp

private abbrev newDecorated := JTGraphCoveredLabelEvaluation.decorated (pointTarget W z)
  (JTSupportedPathGraphData.labels W z L S u hs)
  (JTSupportedPathGraphData.oldTime W z L time S u hs)
  (JTSupportedPathGraphEvaluation.collapse W z L S u hs)
  (JTSupportedPathGraphEvaluation.toPrism W z L time S u hs G)
  (JTSupportedPathGraphData.parameter W z L time S u hs G)

private abbrev oldDecorated := JTGraphCoveredLabelEvaluation.decorated (pointTarget W z)
  L time (collapse W z L) G.projection G.parameter

private theorem newDecorated_cylinder (p : First W z L S u hs) :
    (newInl W z L time S u hs G).app p ≫
      ((newDecorated W z L time S u hs G).app
        ((zeroSection W z L S u hs).obj p)).right =
    lift ((JTSupportedPathGraphEvaluation.toPrism W z L time S u hs G).app
        ((zeroSection W z L S u hs).obj p) ≫
        fst ((codes L).obj ((original W z L S u hs).obj p)).toSSet
          (J.obj (time.obj ((original W z L S u hs).obj p))))
      ((JTSupportedPathGraphData.parameter W z L time S u hs G).app
        ((zeroSection W z L S u hs).obj p)) ≫
      (JTNecklaceEndpointCylinder.cylinder
        ((codes L).obj ((original W z L S u hs).obj p))).app
        ((JTSupportedPathChainLabels.ordinals W z L S u hs).obj
          ((zeroSection W z L S u hs).obj p)) := by
  exact JTEndpointReducedCover.descend_cylinder _ _ _ _ _ _

private theorem oldDecorated_cylinder (p : First W z L S u hs) :
    (oldInl W z L time S u hs G).app p ≫
      ((oldDecorated W z L time S u G).app
        ((original W z L S u hs).obj p)).right =
    lift (G.projection.app ((original W z L S u hs).obj p) ≫
        fst ((codes L).obj ((original W z L S u hs).obj p)).toSSet
          (J.obj (time.obj ((original W z L S u hs).obj p))))
      (G.parameter.app ((original W z L S u hs).obj p)) ≫
      (JTNecklaceEndpointCylinder.cylinder
        ((codes L).obj ((original W z L S u hs).obj p))).app
        ((K W z L).obj ((original W z L S u hs).obj p)) := by
  exact JTEndpointReducedCover.descend_cylinder _ _ _ _ _ _

private theorem cylinder_parameter_comp {T : NecklaceCode} {X : SSet.{0}}
    {k l : SimplexCategory} (g : k ⟶ l) (r : X ⟶ T.toSSet)
    (η : X ⟶ J.obj k) :
    (lift r η ≫ (JTNecklaceEndpointCylinder.cylinder T).app k) ≫
      (JTNecklaceEndpointCylinder.value T).map g =
    lift r (η ≫ J.map g) ≫
      (JTNecklaceEndpointCylinder.cylinder T).app l := by
  have h : lift r η ≫ (𝟙 T.toSSet ⊗ₘ J.map g) =
      lift r (η ≫ J.map g) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, tensorHom_fst, ← Category.assoc, lift_fst]
      exact (Category.comp_id _).trans (lift_fst _ _).symm
    · rw [Category.assoc, tensorHom_snd, ← Category.assoc, lift_snd]
      exact (lift_snd _ _).symm
  rw [Category.assoc, ← (JTNecklaceEndpointCylinder.cylinder T).naturality g]
  change lift r η ≫
    ((𝟙 T.toSSet ⊗ₘ J.map g) ≫
      (JTNecklaceEndpointCylinder.cylinder T).app l) = _
  rw [← Category.assoc, h]

private theorem decorated_square (p : First W z L S u hs) :
    (newDecorated W z L time S u hs G).app
        ((zeroSection W z L S u hs).obj p) ≫
      (underDiagram W z z).map
        ((JTSupportedPathChainEndpoints.zeroToOld W z L S u hs).app p) =
    (sourceChange W z L time S u hs G).app p ≫
      (oldDecorated W z L time S u G).app
        ((original W z L S u hs).obj p) := by
  apply Under.UnderMorphism.ext
  apply (endpointPushout W z L time S u hs G p).hom_ext
  · change ((newInl W z L time S u hs G).app p ≫
        ((newDecorated W z L time S u hs G).app
          ((zeroSection W z L S u hs).obj p)).right) ≫
        ((underDiagram W z z).map
          ((JTSupportedPathChainEndpoints.zeroToOld W z L S u hs).app p)).right =
      ((newInl W z L time S u hs G).app p ≫
        ((sourceChange W z L time S u hs G).app p).right) ≫
        ((oldDecorated W z L time S u G).app
          ((original W z L S u hs).obj p)).right
    rw [newDecorated_cylinder, sourceChange_cylinder]
    conv_rhs => rw [Category.assoc, oldDecorated_cylinder]
    let T := (codes L).obj ((original W z L S u hs).obj p)
    let k := (JTSupportedPathChainLabels.ordinals W z L S u hs).obj
      ((zeroSection W z L S u hs).obj p)
    let g := (JTSupportedPathChainEndpoints.endpointDegree W z L S u hs 0).app p
    let π := (JTSupportedPathGraphEvaluation.toPrism W z L time S u hs G).app
      ((zeroSection W z L S u hs).obj p)
    let θ := (JTSupportedPathGraphData.parameter W z L time S u hs G).app
      ((zeroSection W z L S u hs).obj p)
    let ρ := (graphToOld W z L time S u hs G).app p
    let ψ := G.parameter.app ((original W z L S u hs).obj p)
    change (lift (π ≫ fst T.toSSet (J.obj (time.obj
        ((original W z L S u hs).obj p)))) θ ≫
          (JTNecklaceEndpointCylinder.cylinder T).app k) ≫
        (JTNecklaceEndpointCylinder.nativeMap (𝟙 T) k ≫
          (JTNecklaceEndpointCylinder.value T).map g) =
      ρ ≫ lift (G.projection.app ((original W z L S u hs).obj p) ≫
        fst T.toSSet (J.obj (time.obj ((original W z L S u hs).obj p)))) ψ ≫
          (JTNecklaceEndpointCylinder.cylinder T).app ((K W z L).obj
            ((original W z L S u hs).obj p))
    rw [JTNecklaceEndpointCylinder.nativeMap_id, Category.id_comp,
      cylinder_parameter_comp, zeroParameter_projection]
    dsimp only [π, ρ, ψ]
    rw [graph_square]
    simp only [Category.assoc]
    rfl
  · exact (Under.w ((newDecorated W z L time S u hs G).app
      ((zeroSection W z L S u hs).obj p) ≫
        (underDiagram W z z).map
          ((JTSupportedPathChainEndpoints.zeroToOld W z L S u hs).app p))).trans
        (Under.w ((sourceChange W z L time S u hs G).app p ≫
          (oldDecorated W z L time S u G).app
            ((original W z L S u hs).obj p))).symm

private theorem native_square (p : First W z L S u hs) :
    (JTGraphCoveredLabelEvaluation.nativeLeg (pointTarget W z)
      (JTSupportedPathGraphData.labels W z L S u hs)
      (JTSupportedPathGraphData.oldTime W z L time S u hs)
      (JTSupportedPathGraphEvaluation.collapse W z L S u hs)
      (JTSupportedPathGraphEvaluation.toPrism W z L time S u hs G)).app
        ((zeroSection W z L S u hs).obj p) =
    (sourceChange W z L time S u hs G).app p ≫
      (JTGraphCoveredLabelEvaluation.nativeLeg (pointTarget W z)
        L time (collapse W z L) G.projection).app
        ((original W z L S u hs).obj p) := by
  apply Under.UnderMorphism.ext
  exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

private theorem fixedTarget_square_general
    {a b : OrderedLabelElements.Index W
      (OrderedNecklaceVertexPoints.boundaryPoint W z z)}
    {U V : Under B} (f : a ⟶ b) (r : U ⟶ V)
    (u₀ : U ⟶ (JTTargetCommaPullback.diagram W z z (pointTarget W z)).obj a)
    (v₀ : V ⟶ (JTTargetCommaPullback.diagram W z z (pointTarget W z)).obj b)
    {u₁ : U ⟶ (underDiagram W z z).obj a}
    {v₁ : V ⟶ (underDiagram W z z).obj b}
    {u₂ : U ⟶ BoundaryNecklaceComma.necklaceUnder.obj (pointTarget W z).code}
    {v₂ : V ⟶ BoundaryNecklaceComma.necklaceUnder.obj (pointTarget W z).code}
    (hu₁ : u₀ ≫ JTTargetCommaPullback.fst W z z (pointTarget W z) a = u₁)
    (hv₁ : v₀ ≫ JTTargetCommaPullback.fst W z z (pointTarget W z) b = v₁)
    (hu₂ : u₀ ≫ JTTargetCommaPullback.snd W z z (pointTarget W z) a = u₂)
    (hv₂ : v₀ ≫ JTTargetCommaPullback.snd W z z (pointTarget W z) b = v₂)
    (h₁ : u₁ ≫ (underDiagram W z z).map f = r ≫ v₁)
    (h₂ : u₂ = r ≫ v₂) :
    u₀ ≫ (JTTargetCommaPullback.diagram W z z (pointTarget W z)).map f = r ≫ v₀ := by
  apply (IsPullback.of_hasPullback ((underCocone W z z).app b)
    (JTTargetCommaPullback.targetMap W z z (pointTarget W z))).hom_ext
  · change (u₀ ≫ (JTTargetCommaPullback.diagram W z z (pointTarget W z)).map f) ≫
      JTTargetCommaPullback.fst W z z (pointTarget W z) b =
      (r ≫ v₀) ≫ JTTargetCommaPullback.fst W z z (pointTarget W z) b
    rw [Category.assoc, JTTargetCommaPullback.map_fst W z z (pointTarget W z) f,
      ← Category.assoc u₀, hu₁, Category.assoc r, hv₁]
    exact h₁
  · change (u₀ ≫ (JTTargetCommaPullback.diagram W z z (pointTarget W z)).map f) ≫
      JTTargetCommaPullback.snd W z z (pointTarget W z) b =
      (r ≫ v₀) ≫ JTTargetCommaPullback.snd W z z (pointTarget W z) b
    rw [Category.assoc, JTTargetCommaPullback.map_snd W z z (pointTarget W z) f,
      hu₂, Category.assoc r, hv₂]
    exact h₂

/-- At time zero the full point-target pullback lift commutes with the old
decorated label, original graph, and unchanged native target. -/
theorem fixedTarget_square
    (hu : ∀ a : I, Mono (u.app a)) (p : First W z L S u hs) :
    (JTSupportedPathGraphEvaluation.pullbackLift W z L time S u hs G hu).app
        ((zeroSection W z L S u hs).obj p) ≫
      (JTTargetCommaPullback.diagram W z z (pointTarget W z)).map
        ((JTSupportedPathChainEndpoints.zeroToOld W z L S u hs).app p) =
    (sourceChange W z L time S u hs G).app p ≫
      (oldLift W z L time S u hs G).app ((original W z L S u hs).obj p) := by
  exact fixedTarget_square_general W z
    ((JTSupportedPathChainEndpoints.zeroToOld W z L S u hs).app p)
    ((sourceChange W z L time S u hs G).app p)
    ((JTSupportedPathGraphEvaluation.pullbackLift W z L time S u hs G hu).app
      ((zeroSection W z L S u hs).obj p))
    ((oldLift W z L time S u hs G).app ((original W z L S u hs).obj p))
    (JTDecoratedIntervalCylinder.liftFromProjections_fst _ _ _ _ _ _ _)
    (JTDecoratedIntervalCylinder.liftFromProjections_fst _ _ _ _ _ _ _)
    (JTDecoratedIntervalCylinder.liftFromProjections_snd _ _ _ _ _ _ _)
    (JTDecoratedIntervalCylinder.liftFromProjections_snd _ _ _ _ _ _ _)
    (decorated_square W z L time S u hs G p)
    (native_square W z L time S u hs G p)

private abbrev DQ := JTTargetCommaPullback.diagram W z z (pointTarget W z)
private abbrev endpointLabels := zeroSection W z L S u hs ⋙
  JTSupportedPathGraphData.labels W z L S u hs
private abbrev originalLabels := original W z L S u hs ⋙ L

private def endpointLift (hu : ∀ a : I, Mono (u.app a)) :=
  Functor.whiskerLeft (zeroSection W z L S u hs)
    (JTSupportedPathGraphEvaluation.pullbackLift W z L time S u hs G hu) ≫
      (Functor.associator (zeroSection W z L S u hs)
        (JTSupportedPathGraphData.labels W z L S u hs) (DQ W z)).inv

private def originalLift :=
  Functor.whiskerLeft (original W z L S u hs)
    (oldLift W z L time S u hs G) ≫
      (Functor.associator (original W z L S u hs) L (DQ W z)).inv

private theorem comparison_square (hu : ∀ a : I, Mono (u.app a))
    (p : First W z L S u hs) :
    (endpointLift W z L time S u hs G hu).app p ≫
      (DQ W z).map
        ((JTSupportedPathChainEndpoints.zeroToOld W z L S u hs).app p) =
    (sourceChange W z L time S u hs G).app p ≫
      (originalLift W z L time S u hs G).app p :=
  fixedTarget_square W z L time S u hs G hu p

/-- The complete time-zero presentation compares with the unchanged old
presentation in the same literal point-target comma. Its source change is the
full inverse-image endpoint quotient, and its label change is `zeroToOld`. -/
def zeroComparison (hu : ∀ a : I, Mono (u.app a)) :=
  JTBoundaryNecklacePresentationTransport.comparisonWithSourceChange
    (A := First W z L S u hs)
    (D := JTSupportedPathEndpointPresentation.endpointDiagram
      W z L time S u hs G 0)
    (L := endpointLabels W z L S u hs)
    (D' := original W z L S u hs ⋙ oldReduced W z L time S u G)
    (M := originalLabels W z L S u hs)
    (DQ W z)
    (endpointLift W z L time S u hs G hu)
    (originalLift W z L time S u hs G)
    (sourceChange W z L time S u hs G)
    (JTSupportedPathChainEndpoints.zeroToOld W z L S u hs)
    (comparison_square W z L time S u hs G hu)
    (JTTargetCommaExactEvaluation.fromPresentation W z z (pointTarget W z))

/-- Change every internal-necklace presentation at time zero back to its
unchanged original graph-covered presentation. -/
def toOldPresentation :
    JTSupportedPathEndpointPresentation.Presentation W z L time S u hs G 0 ⥤
      BoundaryNecklaceComma.Presentation (oldReduced W z L time S u G) :=
  Grothendieck.map (Functor.whiskerRight
    (sourceChange W z L time S u hs G) BoundaryNecklaceComma.diagram) ⋙
  Grothendieck.pre (BoundaryNecklaceComma.fiberDiagram
    (oldReduced W z L time S u G)) (original W z L S u hs)

private theorem toOldPresentation_forget :
    toOldPresentation W z L time S u hs G ⋙
      Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram
        (oldReduced W z L time S u G)) =
      JTSupportedPathEndpointPresentation.toOriginal
        W z L time S u hs G 0 := rfl

/-- The complete time-zero presentation comparison is weak on nerves when
the original graph projection is componentwise a trivial fibration. -/
theorem toOldPresentation_weak (hu : ∀ a : I, Mono (u.app a))
    (hG : ∀ a : I, trivialFibrations SSet.{0} (G.projection.app a))
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hp : ∀ a : I, 0 < ((codes L).obj a).len) :
    WeakEquivalence (nerveMap (toOldPresentation W z L time S u hs G)) := by
  letI : WeakEquivalence (nerveMap (Grothendieck.forget
      (BoundaryNecklaceComma.fiberDiagram
        (oldReduced W z L time S u G)))) :=
    JTGraphCoveredPresentationWeak.forget_weak (pointTarget W z) L time
      (collapse W z L) G.projection hG
  have hsource : WeakEquivalence
      (nerveMap (JTSupportedPathEndpointPresentation.toOriginal
        W z L time S u hs G 0)) :=
    JTSupportedPathEndpointPresentation.toOriginal_weak
      W z L time S u hs G hu 0 hG hW hp
  have hcomm : nerveMap (toOldPresentation W z L time S u hs G) ≫
      nerveMap (Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram
        (oldReduced W z L time S u G))) =
      nerveMap (JTSupportedPathEndpointPresentation.toOriginal
        W z L time S u hs G 0) := by
    simpa only [nerveFunctor.map_comp] using
      congrArg nerveMap (toOldPresentation_forget W z L time S u hs G)
  exact weakEquivalence_of_postcomp_of_fac hcomm

end
end DaggerModels.PartII.JTSupportedPathZeroComparison
