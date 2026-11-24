import DaggerModelsPartII.JTSupportedPathWhiskeredRaw
import DaggerModelsPartII.JTSupportedPathWhiskeredEndpointLabels
import DaggerModelsPartII.JTReindexedEndpointCoverTransport
import DaggerModelsPartII.JTGraphCoveredComparisonEquations
import DaggerModelsPartII.JTBoundaryNecklaceTwoReindexComparison
import DaggerModelsPartII.JTGraphCoveredProductInterface
import DaggerModelsPartII.JTGraphCoveredLiftInterface
import DaggerModelsPartII.GrothendieckContractiblePreWeak

/-!
# Whole whiskered path at its zero endpoint

Reuse: `JTSupportedPathWhiskeredRaw.oldRaw` is the supplied raw equation;
`JTComposedPrismLabels.orderedPoint_coefficient` converts it to the ordered
label expected by `JTGraphCoveredLabelEvaluation`. The graph and degree maps
are `JTSupportedPathWhiskeredGraph.toOld/parameter_old/native_square`.
`JTReindexedEndpointCoverTransport.sourceChange` transports the complete
inverse-image endpoint quotient; `JTGraphCoveredComparisonEquations` supplies
the nonterminal native-cylinder and fixed-target pullback equations.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

open CategoryTheory Limits Opposite Simplicial CartesianMonoidalCategory DaggerModels
open HomotopicalAlgebra
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSupportedPathWhiskeredZeroEvaluation

open DecoratedCylinderNecklacePresentation (underDiagram)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev J := GroupoidSimplex.parameter

private def degreeCast {C : Type} [SmallCategory C] {V : Source}
    {p q : Vertex V} {P M R : C ⥤ NecklaceCode}
    {D : C ⥤ SimplexCategory} {Y : C ⥤ SSet.{0}}
    (F : JTVariableMiddleWhiskeredDiagram.Family
      (W := V) (x := p) (y := q) P M R D)
    (θ : Y ⟶ D ⋙ J) :
    Y ⟶ JTParametrizedTargetFamilyComparison.degrees F.labels ⋙ J :=
  θ ≫ eqToHom (congrArg (· ⋙ J)
    (JTGraphCoveredProductInterface.degrees_labels F).symm)

private theorem degreeCast_app {C : Type} [SmallCategory C] {V : Source}
    {p q : Vertex V} {P M R : C ⥤ NecklaceCode}
    {D : C ⥤ SimplexCategory} {Y : C ⥤ SSet.{0}}
    (F : JTVariableMiddleWhiskeredDiagram.Family
      (W := V) (x := p) (y := q) P M R D)
    (θ : Y ⟶ D ⋙ J) (a : C) : (degreeCast F θ).app a = θ.app a := by
  simp only [degreeCast,
    JTGraphCoveredProductInterface.degrees_labels, eqToHom_refl,
    Category.comp_id]

variable {I : Type} [SmallCategory I] (W : Source) (x z y : Vertex W)
variable (L : I ⥤ DecoratedNecklaceHomDiagram.Index W z z)
variable (S : I ⥤ SimplexCategory)
variable (u : S ⟶ JTParametrizedTargetFamilyComparison.degrees L)
variable (hs : ∀ a : I,
  std.map (u.app a) ≫ JTSupportedOrderedCoefficientChoices.old W z L a =
    JTSupportedOrderedCoefficientChoices.supportedConstant W z L S a)
variable (P R : I ⥤ NecklaceCode)
variable (A : JTSupportedPathWhiskeredDiagram.Surroundings W x z y L P R)
variable (time : I ⥤ SimplexCategory)
variable {Y : I ⥤ SSet.{0}}
variable (oldπ : Y ⟶ JTSupportedPathWhiskeredGraph.oldProduct
  W x z y L P R A time)
variable (oldθ : Y ⟶ JTParametrizedTargetFamilyComparison.degrees L ⋙ J)
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (c : JTParametrizedTargetFamilies.codes
  (JTSupportedPathWhiskeredGraph.oldLabels
  W x z y L P R A) ⟶ (Functor.const I).obj Q.code)

private abbrev oldFamily : JTVariableMiddleWhiskeredDiagram.Family
    (W := W) (x := x) (y := y) P (JTParametrizedTargetFamilies.codes L) R
      (JTParametrizedTargetFamilyComparison.degrees L) :=
  JTSupportedPathWhiskeredGraph.oldFamily W x z y L P R A
private abbrev oldLabels :=
  (oldFamily W x z y L P R A).labels
private abbrev oldData (a : I) := JTSupportedPathWhiskeredGraph.oldData
  W x z y L P R A a
private abbrev oldT (a : I) := wedge (P.obj a)
  (wedge ((JTParametrizedTargetFamilies.codes L).obj a) (R.obj a))
private abbrev oldK := JTParametrizedTargetFamilyComparison.degrees L
private abbrev oldH (a : I) : Y.obj a ⟶ (oldT W z L P R a).toSSet :=
  oldπ.app a ≫ fst (oldT W z L P R a).toSSet (J.obj (time.obj a))

private def oldπTarget : Y ⟶
    JTJointRelativeParameters.withTime Q.map J time
      (Over.lift
        (JTParametrizedTargetFamilies.codes (oldLabels W x z y L P R A)) c)
      (JTTargetIntervalOverMapping.whole Q.code) :=
  oldπ ≫ (JTGraphCoveredProductInterface.iso
    (JTParametrizedTargetFamilies.codes (oldLabels W x z y L P R A))
    time Q.code Q.map c).hom

private def oldθTarget : Y ⟶
    JTParametrizedTargetFamilyComparison.degrees
      (oldLabels W x z y L P R A) ⋙ J :=
  degreeCast (oldFamily W x z y L P R A) oldθ

private theorem oldπTarget_app (a : I) :
    (oldπTarget W x z y L P R A time oldπ Q c).app a = oldπ.app a := by
  simp only [oldπTarget, NatTrans.comp_app,
    JTGraphCoveredProductInterface.iso_hom_app, Category.comp_id]

private abbrev oldReduced := JTGraphCoveredLabelEvaluation.reduced Q
  (oldLabels W x z y L P R A) time c
    (oldπTarget W x z y L P R A time oldπ Q c)

variable (oldRaw : ∀ a : I,
  lift (oldH W x z y L P R A time oldπ a) (oldθ.app a) ≫
    JTNecklaceLabelRealization.realizedLabel (oldT W z L P R a).toSSet W
      ((oldK W z L).obj a)
      (SSet.yonedaEquiv (JTComposedPrismLabels.coefficient
        (JTThreePieceLabelOperators.coefficients
          (oldData W x z y L P R A a)))) =
    oldH W x z y L P R A time oldπ a ≫ (c.app a).map ≫ Q.map)

variable (oldMiddleQ : ∀ a : I,
  pullback (oldH W x z y L P R A time oldπ a)
    (tripleRightU (P.obj a)
      ((JTParametrizedTargetFamilies.codes L).obj a) (R.obj a)) ⟶
        J.obj (S.obj a))
variable (oldMiddleFactor : ∀ a : I,
  pullback.fst (oldH W x z y L P R A time oldπ a)
      (tripleRightU (P.obj a)
        ((JTParametrizedTargetFamilies.codes L).obj a) (R.obj a)) ≫
        oldθ.app a = oldMiddleQ a ≫ J.map (u.app a))

include oldRaw in
theorem oldOrderedRaw (a : I) :
    lift (oldH W x z y L P R A time oldπ a) (oldθ.app a) ≫
      JTNecklaceLabelRealization.realizedLabel (oldT W z L P R a).toSSet W
        ((oldK W z L).obj a)
        (JTRealizedLabelEndpoints.orderedLabel W x y
          (oldT W z L P R a) ((oldK W z L).obj a)
          (OrderedLabelElements.label W
            (OrderedNecklaceVertexPoints.boundaryPoint W x y)
            ((oldLabels W x z y L P R A).obj a))) =
    oldH W x z y L P R A time oldπ a ≫ (c.app a).map ≫ Q.map := by
  have hc := JTComposedPrismLabels.orderedPoint_coefficient
    (JTThreePieceLabelOperators.coefficients (oldData W x z y L P R A a))
  change JTRealizedLabelEndpoints.orderedLabel W x y
      (oldT W z L P R a) ((oldK W z L).obj a)
      (OrderedLabelElements.label W
        (OrderedNecklaceVertexPoints.boundaryPoint W x y)
        ((oldLabels W x z y L P R A).obj a)) =
      SSet.yonedaEquiv (JTComposedPrismLabels.coefficient
        (JTThreePieceLabelOperators.coefficients
          (oldData W x z y L P R A a))) at hc
  rw [hc]
  exact oldRaw a

include oldRaw in
private theorem oldOrderedRawTarget (a : I) :
    lift ((oldπTarget W x z y L P R A time oldπ Q c).app a ≫
      fst ((JTParametrizedTargetFamilies.codes
        (oldLabels W x z y L P R A)).obj a).toSSet
        (J.obj (time.obj a)))
      ((oldθTarget W x z y L P R A oldθ).app a) ≫
      JTNecklaceLabelRealization.realizedLabel
        ((JTParametrizedTargetFamilies.codes
          (oldLabels W x z y L P R A)).obj a).toSSet W
        ((JTParametrizedTargetFamilyComparison.degrees
          (oldLabels W x z y L P R A)).obj a)
        (JTRealizedLabelEndpoints.orderedLabel W x y _ _
          (OrderedLabelElements.label W
            (OrderedNecklaceVertexPoints.boundaryPoint W x y)
            ((oldLabels W x z y L P R A).obj a))) =
    ((oldπTarget W x z y L P R A time oldπ Q c).app a ≫
      fst ((JTParametrizedTargetFamilies.codes
        (oldLabels W x z y L P R A)).obj a).toSSet
        (J.obj (time.obj a))) ≫ (c.app a).map ≫ Q.map := by
  rw [oldπTarget_app]
  simp only [oldθTarget, degreeCast_app]
  exact oldOrderedRaw W x z y L P R A time oldπ oldθ Q c oldRaw a

include oldRaw in
def oldEvaluation : BoundaryNecklaceComma.Presentation
    (oldReduced W x z y L P R A time oldπ Q c) ⥤
      JTGraphFactoredPresentation.TargetComma Q :=
  JTGraphCoveredLabelEvaluation.evaluation Q
    (oldLabels W x z y L P R A) time c
    (oldπTarget W x z y L P R A time oldπ Q c)
    (oldθTarget W x z y L P R A oldθ)
    (oldOrderedRawTarget W x z y L P R A time oldπ oldθ Q c oldRaw)

include oldRaw in
def oldLift : oldReduced W x z y L P R A time oldπ Q c ⟶
    oldLabels W x z y L P R A ⋙
      JTTargetCommaPullback.diagram W x y Q :=
  JTDecoratedIntervalCylinder.liftFromProjections Q
    (oldLabels W x z y L P R A)
    (oldReduced W x z y L P R A time oldπ Q c)
    (JTGraphCoveredLabelEvaluation.decorated Q
      (oldLabels W x z y L P R A) time c
      (oldπTarget W x z y L P R A time oldπ Q c)
      (oldθTarget W x z y L P R A oldθ))
    (JTGraphCoveredLabelEvaluation.nativeLeg Q
      (oldLabels W x z y L P R A) time c
      (oldπTarget W x z y L P R A time oldπ Q c))
    (JTGraphCoveredLabelEvaluation.raw_square Q
      (oldLabels W x z y L P R A) time c
      (oldπTarget W x z y L P R A time oldπ Q c)
      (oldθTarget W x z y L P R A oldθ)
      (oldOrderedRawTarget W x z y L P R A time oldπ oldθ Q c oldRaw))

private abbrev pathIndex := JTSupportedPathChainLabels.Index W z L S u hs
private abbrev pathBase := JTSupportedPathChainLabels.toOriginal W z L S u hs
private abbrev pathLabels := JTSupportedPathWhiskeredGraph.pathLabels
  W x z y L S u hs P R A
private abbrev pathTime := pathBase W z L S u hs ⋙ time
private abbrev pathCollapse := JTSupportedPathWhiskeredRaw.collapse
  W x z y L S u hs P R A Q c
private abbrev pathGraph := JTSupportedPathWhiskeredGraph.graph
  W z L S u hs oldθ
private abbrev pathπ := JTSupportedPathWhiskeredGraph.projectionNew
  W x z y L S u hs P R A time oldπ oldθ

private abbrev rawProductEq :
    JTSupportedPathWhiskeredGraph.newProduct
      W x z y L S u hs P R A time =
    pathBase W z L S u hs ⋙
      JTSupportedPathWhiskeredGraph.oldProduct
        W x z y L P R A time := rfl

private def productReindex :
    JTJointRelativeParameters.withTime Q.map J
      (pathTime W z L S u hs time)
      (Over.lift (JTParametrizedTargetFamilies.codes
        (pathLabels W x z y L S u hs P R A))
        (pathCollapse W x z y L S u hs P R A Q c))
      (JTTargetIntervalOverMapping.whole Q.code) ⟶
    pathBase W z L S u hs ⋙
      JTJointRelativeParameters.withTime Q.map J time
        (Over.lift (JTParametrizedTargetFamilies.codes
          (oldLabels W x z y L P R A)) c)
        (JTTargetIntervalOverMapping.whole Q.code) :=
  (JTGraphCoveredProductInterface.iso
      (JTParametrizedTargetFamilies.codes
        (pathLabels W x z y L S u hs P R A))
      (pathTime W z L S u hs time) Q.code Q.map
      (pathCollapse W x z y L S u hs P R A Q c)).inv ≫
    eqToHom (rawProductEq
      W x z y L S u hs P R A time) ≫
    Functor.whiskerLeft (pathBase W z L S u hs)
      (JTGraphCoveredProductInterface.iso
        (JTParametrizedTargetFamilies.codes
          (oldLabels W x z y L P R A)) time Q.code Q.map c).hom

private theorem productReindex_app (p : pathIndex W z L S u hs) :
    (productReindex W x z y L S u hs P R A time Q c).app p = 𝟙 _ := by
  simp only [productReindex, NatTrans.comp_app, Functor.whiskerLeft_app,
    rawProductEq, eqToHom_refl, Category.id_comp,
    JTGraphCoveredProductInterface.iso_hom_app]
  rfl

private theorem graphProduct_square :
    pathπ W x z y L S u hs P R A time oldπ oldθ ≫
      productReindex W x z y L S u hs P R A time Q c =
    JTSupportedPathWhiskeredGraph.toOld W z L S u hs oldθ ≫
      Functor.whiskerLeft (pathBase W z L S u hs)
        (oldπTarget W x z y L P R A time oldπ Q c) := by
  apply NatTrans.ext
  funext p
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    productReindex_app, oldπTarget_app,
    JTSupportedPathWhiskeredGraph.projectionNew_app]
  rfl

private abbrev First := JTSupportedPathChainLabels.First W z L S u hs
private abbrev zeroSection :=
  JTSupportedPathChainEndpoints.endpointSection W z L S u hs 0
private abbrev original :=
  zeroSection W z L S u hs ⋙ pathBase W z L S u hs

private def graphToOld :
    zeroSection W z L S u hs ⋙ pathGraph W z L S u hs oldθ ⟶
    original W z L S u hs ⋙ Y :=
  Functor.whiskerLeft (zeroSection W z L S u hs)
    (JTSupportedPathWhiskeredGraph.toOld W z L S u hs oldθ)

private def productToOld :
    zeroSection W z L S u hs ⋙
      JTJointRelativeParameters.withTime Q.map J
        (pathTime W z L S u hs time)
        (Over.lift (JTParametrizedTargetFamilies.codes
          (pathLabels W x z y L S u hs P R A))
          (pathCollapse W x z y L S u hs P R A Q c))
        (JTTargetIntervalOverMapping.whole Q.code) ⟶
    original W z L S u hs ⋙
      JTJointRelativeParameters.withTime Q.map J time
        (Over.lift (JTParametrizedTargetFamilies.codes
          (oldLabels W x z y L P R A)) c)
        (JTTargetIntervalOverMapping.whole Q.code) :=
  Functor.whiskerLeft (zeroSection W z L S u hs)
    (productReindex W x z y L S u hs P R A time Q c)

private theorem graphToOld_square :
    graphToOld W z L S u hs oldθ ≫
      Functor.whiskerLeft (original W z L S u hs)
        (oldπTarget W x z y L P R A time oldπ Q c) =
    Functor.whiskerLeft (zeroSection W z L S u hs)
      (pathπ W x z y L S u hs P R A time oldπ oldθ) ≫
        productToOld W x z y L S u hs P R A time Q c := by
  have h := congrArg (Functor.whiskerLeft (zeroSection W z L S u hs))
    (graphProduct_square W x z y L S u hs P R A time oldπ oldθ Q c)
  simpa only [graphToOld, productToOld, Functor.whiskerLeft_comp] using h.symm

private abbrev oldBoundary := JTGraphCoveredLabelEvaluation.boundary Q
  (oldLabels W x z y L P R A) time c
private abbrev pathBoundary := JTGraphCoveredLabelEvaluation.boundary Q
  (pathLabels W x z y L S u hs P R A)
  (pathTime W z L S u hs time)
  (pathCollapse W x z y L S u hs P R A Q c)
private abbrev oldE := Functor.whiskerLeft time
  JTXiEndpointCollapse.cylinderProjection
private abbrev pathE := Functor.whiskerLeft
  (pathTime W z L S u hs time)
  JTXiEndpointCollapse.cylinderProjection

private def boundaryToOld :
    pathTime W z L S u hs time ⋙ JTXiEndpointCollapse.boundaryCylinder ⟶
    pathBase W z L S u hs ⋙
      (time ⋙ JTXiEndpointCollapse.boundaryCylinder) := 𝟙 _

private theorem boundary_square :
    pathBoundary W x z y L S u hs P R A time Q c ≫
      productReindex W x z y L S u hs P R A time Q c =
    boundaryToOld W z L S u hs time ≫
      Functor.whiskerLeft (pathBase W z L S u hs)
        (oldBoundary W x z y L P R A time Q c) := by
  apply NatTrans.ext
  funext p
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    productReindex_app, Category.comp_id, boundaryToOld]
  rfl

private theorem endpoint_square (p : pathIndex W z L S u hs) :
    (boundaryToOld W z L S u hs time).app p ≫
      (oldE time).app ((pathBase W z L S u hs).obj p) =
      (pathE W z L S u hs time).app p := by
  rfl

/-- The complete inverse-image endpoint quotient of the whole supported
path maps to the old quotient over the original index. -/
def sourceChangeAll :
    JTSupportedPathWhiskeredRaw.reduced W x z y L S u hs P R A time
      oldπ oldθ Q c ⟶
    pathBase W z L S u hs ⋙
      oldReduced W x z y L P R A time oldπ Q c :=
  JTReindexedEndpointCoverTransport.sourceChange
    (pathBase W z L S u hs)
    (oldπTarget W x z y L P R A time oldπ Q c)
    (oldBoundary W x z y L P R A time Q c) (oldE time)
    (pathπ W x z y L S u hs P R A time oldπ oldθ)
    (pathBoundary W x z y L S u hs P R A time Q c)
    (pathE W z L S u hs time)
    (productReindex W x z y L S u hs P R A time Q c)
    (JTSupportedPathWhiskeredGraph.toOld W z L S u hs oldθ)
    (boundaryToOld W z L S u hs time)
    (graphProduct_square W x z y L S u hs P R A time oldπ oldθ Q c).symm
    (boundary_square W x z y L S u hs P R A time Q c)
    (endpoint_square W z L S u hs time)

/-- Restriction of the complete source change to the zero interval endpoint. -/
def sourceChange0 :
    zeroSection W z L S u hs ⋙
      JTSupportedPathWhiskeredRaw.reduced W x z y L S u hs P R A time
        oldπ oldθ Q c ⟶
    original W z L S u hs ⋙
      oldReduced W x z y L P R A time oldπ Q c :=
  Functor.whiskerLeft (zeroSection W z L S u hs)
    (sourceChangeAll W x z y L S u hs P R A time oldπ oldθ Q c)

private def pathLift (hu : ∀ a : I, Mono (u.app a)) :
    JTSupportedPathWhiskeredRaw.reduced W x z y L S u hs P R A time
      oldπ oldθ Q c ⟶
    pathLabels W x z y L S u hs P R A ⋙
      JTTargetCommaPullback.diagram W x y Q :=
  JTVariableMiddleGraphEvaluation.pullbackLift Q
    (JTSupportedPathWhiskeredDiagram.variableMiddleFamily
      W x z y L S u hs P R A)
    (pathTime W z L S u hs time)
    (pathCollapse W x z y L S u hs P R A Q c)
    (pathπ W x z y L S u hs P R A time oldπ oldθ)
    (JTSupportedPathWhiskeredGraph.parameter W z L S u hs oldθ)
    (JTSupportedPathWhiskeredRaw.pieceEquations
      W x z y L S u hs P R A time oldπ oldθ Q c
      oldRaw oldMiddleQ oldMiddleFactor hu)

private theorem pathNative_square (p : pathIndex W z L S u hs) :
    (pathπ W x z y L S u hs P R A time oldπ oldθ).app p ≫
      fst (oldT W z L P R ((pathBase W z L S u hs).obj p)).toSSet
        (J.obj (time.obj ((pathBase W z L S u hs).obj p))) =
    (JTSupportedPathWhiskeredGraph.toOld W z L S u hs oldθ).app p ≫
      oldH W x z y L P R A time oldπ
        ((pathBase W z L S u hs).obj p) := by
  rw [JTSupportedPathWhiskeredGraph.projectionNew_app]
  rfl

private theorem zeroParameter_projection (p : First W z L S u hs) :
    (JTSupportedPathWhiskeredGraph.parameter W z L S u hs oldθ).app
        ((zeroSection W z L S u hs).obj p) ≫
      J.map ((JTSupportedPathChainEndpoints.endpointDegree W z L S u hs 0).app p) =
    (graphToOld W z L S u hs oldθ).app p ≫
      oldθ.app ((original W z L S u hs).obj p) := by
  exact NatTrans.congr_app
    (JTSupportedPathWhiskeredGraph.parameter_old W z L S u hs oldθ)
    ((zeroSection W z L S u hs).obj p)

private theorem sourceChangeAll_cylinder (p : pathIndex W z L S u hs) :
    (JTGraphCoveredCylinderEquations.inc Q
      (pathLabels W x z y L S u hs P R A)
      (pathTime W z L S u hs time)
      (pathCollapse W x z y L S u hs P R A Q c)
      (pathπ W x z y L S u hs P R A time oldπ oldθ)).app p ≫
        ((sourceChangeAll W x z y L S u hs P R A time oldπ oldθ Q c).app p).right =
    (JTSupportedPathWhiskeredGraph.toOld W z L S u hs oldθ).app p ≫
      (JTGraphCoveredCylinderEquations.inc Q
        (oldLabels W x z y L P R A) time c
        (oldπTarget W x z y L P R A time oldπ Q c)).app
          ((pathBase W z L S u hs).obj p) :=
  JTReindexedEndpointCoverTransport.sourceChange_cylinder
    (pathBase W z L S u hs)
    (oldπTarget W x z y L P R A time oldπ Q c)
    (oldBoundary W x z y L P R A time Q c) (oldE time)
    (pathπ W x z y L S u hs P R A time oldπ oldθ)
    (pathBoundary W x z y L S u hs P R A time Q c)
    (pathE W z L S u hs time)
    (productReindex W x z y L S u hs P R A time Q c)
    (JTSupportedPathWhiskeredGraph.toOld W z L S u hs oldθ)
    (boundaryToOld W z L S u hs time)
    (graphProduct_square W x z y L S u hs P R A time oldπ oldθ Q c).symm
    (boundary_square W x z y L S u hs P R A time Q c)
    (endpoint_square W z L S u hs time) p

private abbrev newDecorated := JTGraphCoveredLabelEvaluation.decorated Q
  (pathLabels W x z y L S u hs P R A)
  (pathTime W z L S u hs time)
  (pathCollapse W x z y L S u hs P R A Q c)
  (pathπ W x z y L S u hs P R A time oldπ oldθ)
  (JTSupportedPathWhiskeredGraph.parameter W z L S u hs oldθ)
private abbrev oldDecorated := JTGraphCoveredLabelEvaluation.decorated Q
  (oldLabels W x z y L P R A) time c
  (oldπTarget W x z y L P R A time oldπ Q c)
  (oldθTarget W x z y L P R A oldθ)

private theorem newDecorated_cylinder (p : pathIndex W z L S u hs) :
    (JTGraphCoveredCylinderEquations.inc Q
      (pathLabels W x z y L S u hs P R A)
      (pathTime W z L S u hs time)
      (pathCollapse W x z y L S u hs P R A Q c)
      (pathπ W x z y L S u hs P R A time oldπ oldθ)).app p ≫
        ((newDecorated W x z y L S u hs P R A time oldπ oldθ Q c).app p).right =
    lift ((pathπ W x z y L S u hs P R A time oldπ oldθ).app p ≫
        fst (oldT W z L P R ((pathBase W z L S u hs).obj p)).toSSet
          (J.obj (time.obj ((pathBase W z L S u hs).obj p))))
      ((JTSupportedPathWhiskeredGraph.parameter W z L S u hs oldθ).app p) ≫
        (JTNecklaceEndpointCylinder.cylinder
          (oldT W z L P R ((pathBase W z L S u hs).obj p))).app
            ((JTSupportedPathChainLabels.ordinals W z L S u hs).obj p) :=
  JTGraphCoveredCylinderEquations.decorated_cylinder Q
    (pathLabels W x z y L S u hs P R A)
    (pathTime W z L S u hs time)
    (pathCollapse W x z y L S u hs P R A Q c)
    (pathπ W x z y L S u hs P R A time oldπ oldθ)
    (JTSupportedPathWhiskeredGraph.parameter W z L S u hs oldθ) p

private abbrev newNative := JTGraphCoveredLabelEvaluation.nativeLeg Q
  (pathLabels W x z y L S u hs P R A)
  (pathTime W z L S u hs time)
  (pathCollapse W x z y L S u hs P R A Q c)
  (pathπ W x z y L S u hs P R A time oldπ oldθ)
private abbrev oldNative := JTGraphCoveredLabelEvaluation.nativeLeg Q
  (oldLabels W x z y L P R A) time c
  (oldπTarget W x z y L P R A time oldπ Q c)

private theorem pathPushout (p : pathIndex W z L S u hs) :
    IsPushout
      ((JTEndpointReducedPullbackCover.boundaryInclusion
        (pathπ W x z y L S u hs P R A time oldπ oldθ)
        (pathBoundary W x z y L S u hs P R A time Q c)).app p)
      ((JTEndpointReducedPullbackCover.collapse
        (pathπ W x z y L S u hs P R A time oldπ oldθ)
        (pathBoundary W x z y L S u hs P R A time Q c)
        (pathE W z L S u hs time)).app p)
      ((JTGraphCoveredCylinderEquations.inc Q
        (pathLabels W x z y L S u hs P R A)
        (pathTime W z L S u hs time)
        (pathCollapse W x z y L S u hs P R A Q c)
        (pathπ W x z y L S u hs P R A time oldπ oldθ)).app p)
      ((pushout.inr
        (JTEndpointReducedPullbackCover.boundaryInclusion
          (pathπ W x z y L S u hs P R A time oldπ oldθ)
          (pathBoundary W x z y L S u hs P R A time Q c))
        (JTEndpointReducedPullbackCover.collapse
          (pathπ W x z y L S u hs P R A time oldπ oldθ)
          (pathBoundary W x z y L S u hs P R A time Q c)
          (pathE W z L S u hs time))).app p) :=
  (IsPushout.of_hasPushout
    (JTEndpointReducedPullbackCover.boundaryInclusion
      (pathπ W x z y L S u hs P R A time oldπ oldθ)
      (pathBoundary W x z y L S u hs P R A time Q c))
    (JTEndpointReducedPullbackCover.collapse
      (pathπ W x z y L S u hs P R A time oldπ oldθ)
      (pathBoundary W x z y L S u hs P R A time Q c)
      (pathE W z L S u hs time))).map
    ((CategoryTheory.evaluation (pathIndex W z L S u hs) SSet.{0}).obj p)

private theorem native_square_all (p : pathIndex W z L S u hs) :
    (newNative W x z y L S u hs P R A time oldπ oldθ Q c).app p =
    (sourceChangeAll W x z y L S u hs P R A time oldπ oldθ Q c).app p ≫
      (oldNative W x z y L P R A time oldπ Q c).app
        ((pathBase W z L S u hs).obj p) := by
  apply Under.UnderMorphism.ext
  apply (pathPushout W x z y L S u hs P R A time oldπ oldθ Q c p).hom_ext
  · change ((JTGraphCoveredCylinderEquations.inc Q
        (pathLabels W x z y L S u hs P R A)
        (pathTime W z L S u hs time)
        (pathCollapse W x z y L S u hs P R A Q c)
        (pathπ W x z y L S u hs P R A time oldπ oldθ)).app p ≫
          ((newNative W x z y L S u hs P R A time oldπ oldθ Q c).app p).right) =
      ((JTGraphCoveredCylinderEquations.inc Q
        (pathLabels W x z y L S u hs P R A)
        (pathTime W z L S u hs time)
        (pathCollapse W x z y L S u hs P R A Q c)
        (pathπ W x z y L S u hs P R A time oldπ oldθ)).app p ≫
          ((sourceChangeAll W x z y L S u hs P R A time oldπ oldθ Q c).app p).right) ≫
            ((oldNative W x z y L P R A time oldπ Q c).app
              ((pathBase W z L S u hs).obj p)).right
    rw [JTGraphCoveredComparisonEquations.native_cylinder,
      sourceChangeAll_cylinder, Category.assoc,
      JTGraphCoveredComparisonEquations.native_cylinder]
    rw [oldπTarget_app]
    change ((pathπ W x z y L S u hs P R A time oldπ oldθ).app p ≫
        fst (oldT W z L P R ((pathBase W z L S u hs).obj p)).toSSet
          (J.obj (time.obj ((pathBase W z L S u hs).obj p)))) ≫
          (c.app ((pathBase W z L S u hs).obj p)).map =
      ((JTSupportedPathWhiskeredGraph.toOld W z L S u hs oldθ).app p ≫
        oldH W x z y L P R A time oldπ
          ((pathBase W z L S u hs).obj p)) ≫
          (c.app ((pathBase W z L S u hs).obj p)).map
    exact congrArg (· ≫ (c.app ((pathBase W z L S u hs).obj p)).map)
      (pathNative_square W x z y L S u hs P R A time oldπ oldθ p)
  · exact (Under.w ((newNative W x z y L S u hs P R A time oldπ oldθ Q c).app p)).trans
      (Under.w ((sourceChangeAll W x z y L S u hs P R A time oldπ oldθ Q c).app p ≫
        (oldNative W x z y L P R A time oldπ Q c).app
          ((pathBase W z L S u hs).obj p))).symm

private abbrev proj := OrderedLabelElements.projection W
  (OrderedNecklaceVertexPoints.boundaryPoint W x y)

private theorem zeroNative_id (p : First W z L S u hs) :
    ((proj W x y).map
      ((JTSupportedPathWhiskeredEndpointLabels.zeroToOld
        W x z y L S u hs P R A).app p)).1 =
      𝟙 (oldT W z L P R ((original W z L S u hs).obj p)) := by
  have h := congrArg Prod.fst
    (JTSupportedPathWhiskeredEndpointLabels.zeroToOld_projection
      W x z y L S u hs P R A p)
  change _ = _ at h
  rw [h]
  change wedgeMap (𝟙 (P.obj ((original W z L S u hs).obj p)))
      (wedgeMap
        (𝟙 ((JTParametrizedTargetFamilies.codes L).obj
          ((original W z L S u hs).obj p)))
        (𝟙 (R.obj ((original W z L S u hs).obj p)))) =
      𝟙 (oldT W z L P R ((original W z L S u hs).obj p))
  exact (congrArg (wedgeMap
    (𝟙 (P.obj ((original W z L S u hs).obj p))))
    (wedgeMap_id
      (T := (JTParametrizedTargetFamilies.codes L).obj
        ((original W z L S u hs).obj p))
      (U := R.obj ((original W z L S u hs).obj p)))).trans
    (wedgeMap_id
      (T := P.obj ((original W z L S u hs).obj p))
      (U := wedge ((JTParametrizedTargetFamilies.codes L).obj
        ((original W z L S u hs).obj p))
        (R.obj ((original W z L S u hs).obj p))))

private theorem zeroOrdinal (p : First W z L S u hs) :
    ((proj W x y).map
      ((JTSupportedPathWhiskeredEndpointLabels.zeroToOld
        W x z y L S u hs P R A).app p)).2 =
      (JTSupportedPathChainEndpoints.endpointDegree W z L S u hs 0).app p :=
  congrArg Prod.snd
    (JTSupportedPathWhiskeredEndpointLabels.zeroToOld_projection
      W x z y L S u hs P R A p)

private theorem decorated_square (p : First W z L S u hs) :
    (newDecorated W x z y L S u hs P R A time oldπ oldθ Q c).app
        ((zeroSection W z L S u hs).obj p) ≫
      (underDiagram W x y).map
        ((JTSupportedPathWhiskeredEndpointLabels.zeroToOld
          W x z y L S u hs P R A).app p) =
    (sourceChange0 W x z y L S u hs P R A time oldπ oldθ Q c).app p ≫
      (oldDecorated W x z y L P R A time oldπ oldθ Q c).app
        ((original W z L S u hs).obj p) := by
  let p₀ := (zeroSection W z L S u hs).obj p
  let a := (original W z L S u hs).obj p
  let T := oldT W z L P R a
  let k := (JTSupportedPathChainLabels.ordinals W z L S u hs).obj p₀
  let l := (oldK W z L).obj a
  let f := ((proj W x y).map
    ((JTSupportedPathWhiskeredEndpointLabels.zeroToOld
      W x z y L S u hs P R A).app p)).1
  let α := ((proj W x y).map
    ((JTSupportedPathWhiskeredEndpointLabels.zeroToOld
      W x z y L S u hs P R A).app p)).2
  let h := (pathπ W x z y L S u hs P R A time oldπ oldθ).app p₀ ≫
    fst T.toSSet (J.obj (time.obj a))
  let θ := (JTSupportedPathWhiskeredGraph.parameter W z L S u hs oldθ).app p₀
  let h' := (oldπTarget W x z y L P R A time oldπ Q c).app a ≫
    fst T.toSSet (J.obj (time.obj a))
  let θ' := (oldθTarget W x z y L P R A oldθ).app a
  let η := (JTSupportedPathWhiskeredGraph.toOld W z L S u hs oldθ).app p₀
  have hf : f = 𝟙 T := zeroNative_id W x z y L S u hs P R A p
  have hα : α =
      (JTSupportedPathChainEndpoints.endpointDegree W z L S u hs 0).app p :=
    zeroOrdinal W x z y L S u hs P R A p
  have hn : h ≫ f.map = η ≫ h' := by
    rw [hf]
    change h = η ≫ h'
    dsimp only [h']
    rw [oldπTarget_app]
    exact pathNative_square W x z y L S u hs P R A time oldπ oldθ p₀
  have hθ : θ ≫ J.map α = η ≫ θ' := by
    rw [hα]
    change θ ≫ J.map
        ((JTSupportedPathChainEndpoints.endpointDegree W z L S u hs 0).app p) =
      η ≫ (degreeCast (oldFamily W x z y L P R A) oldθ).app a
    rw [degreeCast_app]
    exact zeroParameter_projection W z L S u hs oldθ p
  apply Under.UnderMorphism.ext
  apply (pathPushout W x z y L S u hs P R A time oldπ oldθ Q c p₀).hom_ext
  · change ((JTGraphCoveredCylinderEquations.inc Q
        (pathLabels W x z y L S u hs P R A)
        (pathTime W z L S u hs time)
        (pathCollapse W x z y L S u hs P R A Q c)
        (pathπ W x z y L S u hs P R A time oldπ oldθ)).app p₀ ≫
          ((newDecorated W x z y L S u hs P R A time oldπ oldθ Q c).app p₀).right) ≫
        ((underDiagram W x y).map
          ((JTSupportedPathWhiskeredEndpointLabels.zeroToOld
            W x z y L S u hs P R A).app p)).right =
      ((JTGraphCoveredCylinderEquations.inc Q
        (pathLabels W x z y L S u hs P R A)
        (pathTime W z L S u hs time)
        (pathCollapse W x z y L S u hs P R A Q c)
        (pathπ W x z y L S u hs P R A time oldπ oldθ)).app p₀ ≫
          ((sourceChangeAll W x z y L S u hs P R A time oldπ oldθ Q c).app p₀).right) ≫
        ((oldDecorated W x z y L P R A time oldπ oldθ Q c).app a).right
    rw [newDecorated_cylinder, sourceChangeAll_cylinder]
    have hOld :
        (JTGraphCoveredCylinderEquations.inc Q
          (oldLabels W x z y L P R A) time c
          (oldπTarget W x z y L P R A time oldπ Q c)).app
            ((pathBase W z L S u hs).obj p₀) ≫
          ((oldDecorated W x z y L P R A time oldπ oldθ Q c).app a).right =
        lift h' θ' ≫ (JTNecklaceEndpointCylinder.cylinder T).app l := by
      exact JTGraphCoveredCylinderEquations.decorated_cylinder Q
        (oldLabels W x z y L P R A) time c
        (oldπTarget W x z y L P R A time oldπ Q c)
        (oldθTarget W x z y L P R A oldθ) a
    conv_rhs => rw [Category.assoc, hOld]
    change (lift h θ ≫ (JTNecklaceEndpointCylinder.cylinder T).app k) ≫
        (NecklaceCylinderJointDiagram.cylinderUnder.map
          (show (T, k) ⟶ (T, l) from (f, α))).right =
      η ≫ lift h' θ' ≫ (JTNecklaceEndpointCylinder.cylinder T).app l
    exact JTGraphCoveredComparisonEquations.graph_cylinder_map
      f α h θ h' θ' η hn hθ
  · exact (Under.w ((newDecorated W x z y L S u hs P R A time oldπ oldθ Q c).app p₀ ≫
      (underDiagram W x y).map
        ((JTSupportedPathWhiskeredEndpointLabels.zeroToOld
          W x z y L S u hs P R A).app p))).trans
      (Under.w ((sourceChange0 W x z y L S u hs P R A time oldπ oldθ Q c).app p ≫
        (oldDecorated W x z y L P R A time oldπ oldθ Q c).app a)).symm

include oldRaw oldMiddleQ oldMiddleFactor in
/-- Exact fixed-`Q` square at time zero, including both the decorated and
native target legs of every internal-necklace presentation. -/
theorem fixedTarget_square (hu : ∀ a : I, Mono (u.app a))
    (p : First W z L S u hs) :
    (pathLift W x z y L S u hs P R A time oldπ oldθ Q c
      oldRaw oldMiddleQ oldMiddleFactor hu).app
        ((zeroSection W z L S u hs).obj p) ≫
      (JTTargetCommaPullback.diagram W x y Q).map
        ((JTSupportedPathWhiskeredEndpointLabels.zeroToOld
          W x z y L S u hs P R A).app p) =
    (sourceChange0 W x z y L S u hs P R A time oldπ oldθ Q c).app p ≫
      (oldLift W x z y L P R A time oldπ oldθ Q c oldRaw).app
        ((original W z L S u hs).obj p) := by
  exact JTGraphCoveredComparisonEquations.fixedTarget_square Q
    ((JTSupportedPathWhiskeredEndpointLabels.zeroToOld
      W x z y L S u hs P R A).app p)
    ((sourceChange0 W x z y L S u hs P R A time oldπ oldθ Q c).app p)
    ((pathLift W x z y L S u hs P R A time oldπ oldθ Q c
      oldRaw oldMiddleQ oldMiddleFactor hu).app
        ((zeroSection W z L S u hs).obj p))
    ((oldLift W x z y L P R A time oldπ oldθ Q c oldRaw).app
      ((original W z L S u hs).obj p))
    (JTDecoratedIntervalCylinder.liftFromProjections_fst _ _ _ _ _ _ _)
    (JTDecoratedIntervalCylinder.liftFromProjections_fst _ _ _ _ _ _ _)
    (JTDecoratedIntervalCylinder.liftFromProjections_snd _ _ _ _ _ _ _)
    (JTDecoratedIntervalCylinder.liftFromProjections_snd _ _ _ _ _ _ _)
    (decorated_square W x z y L S u hs P R A time oldπ oldθ Q c p)
    (native_square_all W x z y L S u hs P R A time oldπ oldθ Q c
      ((zeroSection W z L S u hs).obj p))

include oldRaw in
theorem oldEvaluation_eq_mapPresentation :
    oldEvaluation W x z y L P R A time oldπ oldθ Q c oldRaw =
      JTBoundaryNecklacePresentationCone.mapPresentation
        (JTTargetCommaPullback.diagram W x y Q)
        (oldReduced W x z y L P R A time oldπ Q c)
        (oldLabels W x z y L P R A)
        (oldLift W x z y L P R A time oldπ oldθ Q c oldRaw) ⋙
      JTTargetCommaExactEvaluation.fromPresentation W x y Q :=
  JTGraphCoveredLiftInterface.evaluation_eq_mapPresentation Q
    (oldLabels W x z y L P R A) time c
    (oldπTarget W x z y L P R A time oldπ Q c)
    (oldθTarget W x z y L P R A oldθ)
    (oldOrderedRawTarget W x z y L P R A time oldπ oldθ Q c oldRaw)

include oldRaw oldMiddleQ oldMiddleFactor in
theorem pathEvaluation_eq_mapPresentation (hu : ∀ a : I, Mono (u.app a)) :
    JTSupportedPathWhiskeredRaw.evaluation W x z y L S u hs P R A time
      oldπ oldθ Q c oldRaw oldMiddleQ oldMiddleFactor hu =
      JTBoundaryNecklacePresentationCone.mapPresentation
        (JTTargetCommaPullback.diagram W x y Q)
        (JTSupportedPathWhiskeredRaw.reduced W x z y L S u hs P R A time
          oldπ oldθ Q c)
        (pathLabels W x z y L S u hs P R A)
        (pathLift W x z y L S u hs P R A time oldπ oldθ Q c
          oldRaw oldMiddleQ oldMiddleFactor hu) ⋙
      JTTargetCommaExactEvaluation.fromPresentation W x y Q :=
  JTVariableMiddleGraphEvaluation.evaluation_eq_mapPresentation Q
    (JTSupportedPathWhiskeredDiagram.variableMiddleFamily
      W x z y L S u hs P R A)
    (pathTime W z L S u hs time)
    (pathCollapse W x z y L S u hs P R A Q c)
    (pathπ W x z y L S u hs P R A time oldπ oldθ)
    (JTSupportedPathWhiskeredGraph.parameter W z L S u hs oldθ)
    (JTSupportedPathWhiskeredRaw.pieceEquations
      W x z y L S u hs P R A time oldπ oldθ Q c
      oldRaw oldMiddleQ oldMiddleFactor hu)

include oldRaw oldMiddleQ oldMiddleFactor in
/-- Comparison of all internal-necklace evaluations after two independent
reindexings, in the literal unchanged target comma category `Q`. -/
def zeroComparison (hu : ∀ a : I, Mono (u.app a)) :=
  JTBoundaryNecklaceTwoReindexComparison.comparison
    (E := JTTargetCommaPullback.diagram W x y Q)
    (F := JTSupportedPathWhiskeredRaw.reduced W x z y L S u hs P R A
      time oldπ oldθ Q c)
    (L := pathLabels W x z y L S u hs P R A)
    (p := pathLift W x z y L S u hs P R A time oldπ oldθ Q c
      oldRaw oldMiddleQ oldMiddleFactor hu)
    (G := zeroSection W z L S u hs)
    (F' := oldReduced W x z y L P R A time oldπ Q c)
    (M := oldLabels W x z y L P R A)
    (q := oldLift W x z y L P R A time oldπ oldθ Q c oldRaw)
    (G' := original W z L S u hs)
    (s := sourceChange0 W x z y L S u hs P R A time oldπ oldθ Q c)
    (r := JTSupportedPathWhiskeredEndpointLabels.zeroToOld
      W x z y L S u hs P R A)
    (h := fixedTarget_square W x z y L S u hs P R A time
      oldπ oldθ Q c oldRaw oldMiddleQ oldMiddleFactor hu)
    (JTTargetCommaExactEvaluation.fromPresentation W x y Q)

/-- Full internal-necklace presentation on the zero endpoint face. -/
abbrev endpointPresentation := BoundaryNecklaceComma.Presentation
  (zeroSection W z L S u hs ⋙
    JTSupportedPathWhiskeredRaw.reduced W x z y L S u hs P R A
      time oldπ oldθ Q c)

/-- Insert the zero endpoint presentation into the complete path presentation. -/
abbrev endpointInclusion : endpointPresentation W x z y L S u hs P R A
    time oldπ oldθ Q c ⥤
    BoundaryNecklaceComma.Presentation
      (JTSupportedPathWhiskeredRaw.reduced W x z y L S u hs P R A
        time oldπ oldθ Q c) :=
  Grothendieck.pre (BoundaryNecklaceComma.fiberDiagram
    (JTSupportedPathWhiskeredRaw.reduced W x z y L S u hs P R A
      time oldπ oldθ Q c)) (zeroSection W z L S u hs)

include oldRaw oldMiddleQ oldMiddleFactor in
/-- Exact time-zero evaluation of every internal necklace in fixed `Q`. -/
def endpointEvaluation (hu : ∀ a : I, Mono (u.app a)) :
    endpointPresentation W x z y L S u hs P R A time oldπ oldθ Q c ⥤
      JTGraphFactoredPresentation.TargetComma Q :=
  endpointInclusion W x z y L S u hs P R A time oldπ oldθ Q c ⋙
    JTSupportedPathWhiskeredRaw.evaluation W x z y L S u hs P R A
      time oldπ oldθ Q c oldRaw oldMiddleQ oldMiddleFactor hu

/-- Map the full zero endpoint presentation to the unchanged old
graph-covered presentation, with its entire inverse-image boundary. -/
def toOldPresentation :
    endpointPresentation W x z y L S u hs P R A time oldπ oldθ Q c ⥤
    BoundaryNecklaceComma.Presentation
      (oldReduced W x z y L P R A time oldπ Q c) :=
  Grothendieck.map (Functor.whiskerRight
    (sourceChange0 W x z y L S u hs P R A time oldπ oldθ Q c)
    BoundaryNecklaceComma.diagram) ⋙
  Grothendieck.pre (BoundaryNecklaceComma.fiberDiagram
    (oldReduced W x z y L P R A time oldπ Q c))
    (original W z L S u hs)

include oldRaw oldMiddleQ oldMiddleFactor in
/-- Typed comparison from the exact zero endpoint evaluation to the old
evaluation after transport of every internal necklace. -/
def evaluationComparison (hu : ∀ a : I, Mono (u.app a)) :
    endpointEvaluation W x z y L S u hs P R A time oldπ oldθ Q c
      oldRaw oldMiddleQ oldMiddleFactor hu ⟶
    toOldPresentation W x z y L S u hs P R A time oldπ oldθ Q c ⋙
      oldEvaluation W x z y L P R A time oldπ oldθ Q c oldRaw := by
  rw [endpointEvaluation, pathEvaluation_eq_mapPresentation
    W x z y L S u hs P R A time oldπ oldθ Q c
      oldRaw oldMiddleQ oldMiddleFactor hu]
  rw [oldEvaluation_eq_mapPresentation
    W x z y L P R A time oldπ oldθ Q c oldRaw]
  exact zeroComparison W x z y L S u hs P R A time oldπ oldθ Q c
    oldRaw oldMiddleQ oldMiddleFactor hu

/-- The zero endpoint inclusion is weak whenever the original whole graph
projection is componentwise a trivial fibration. -/
theorem endpointInclusion_weak
    (hπ : ∀ a : I, trivialFibrations SSet.{0} (oldπ.app a)) :
    WeakEquivalence (nerveMap
      (endpointInclusion W x z y L S u hs P R A time oldπ oldθ Q c)) := by
  apply GrothendieckContractiblePreWeak.pre_weak
  · intro p
    apply JTGraphCoveredPresentationWeak.fiber_point_GW Q
      (pathLabels W x z y L S u hs P R A)
      (pathTime W z L S u hs time)
      (pathCollapse W x z y L S u hs P R A Q c)
      (pathπ W x z y L S u hs P R A time oldπ oldθ)
    intro q
    rw [JTSupportedPathWhiskeredGraph.projectionNew_app]
    exact JTSupportedPathWhiskeredGraph.projection_trivialFibration
      W x z y L S u hs P R A time oldπ oldθ hπ q
  · exact JTSupportedPathChainEndpoints.endpointSection_weak
      W z L S u hs 0

/-- The old presentation forgets to the same original index reached by the
zero endpoint presentation. -/
private theorem toOldPresentation_forget :
    toOldPresentation W x z y L S u hs P R A time oldπ oldθ Q c ⋙
      Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram
        (oldReduced W x z y L P R A time oldπ Q c)) =
    endpointInclusion W x z y L S u hs P R A time oldπ oldθ Q c ⋙
      JTSupportedPathWhiskeredRaw.toOriginal W x z y L S u hs P R A
        time oldπ oldθ Q c := rfl

/-- Weak equivalence of the complete old-presentation comparison. Its
proof only uses weak projections to the common original index. -/
theorem toOldPresentation_weak
    (hu : ∀ a : I, Mono (u.app a))
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hp : ∀ a : I,
      0 < ((JTParametrizedTargetFamilies.codes L).obj a).len)
    (hπ : ∀ a : I, trivialFibrations SSet.{0} (oldπ.app a)) :
    WeakEquivalence (nerveMap
      (toOldPresentation W x z y L S u hs P R A time oldπ oldθ Q c)) := by
  letI : WeakEquivalence (nerveMap
      (Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram
        (oldReduced W x z y L P R A time oldπ Q c)))) := by
    apply JTGraphCoveredPresentationWeak.forget_weak Q
      (oldLabels W x z y L P R A) time c
      (oldπTarget W x z y L P R A time oldπ Q c)
    intro a
    rw [oldπTarget_app]
    exact hπ a
  haveI : WeakEquivalence (nerveMap
      (endpointInclusion W x z y L S u hs P R A time oldπ oldθ Q c)) :=
    endpointInclusion_weak W x z y L S u hs P R A time oldπ oldθ Q c hπ
  haveI : WeakEquivalence (nerveMap
      (JTSupportedPathWhiskeredRaw.toOriginal W x z y L S u hs P R A
        time oldπ oldθ Q c)) :=
    JTSupportedPathWhiskeredRaw.toOriginal_weak
      W x z y L S u hs P R A time oldπ oldθ Q c hu hW hp hπ
  have hsource : WeakEquivalence (nerveMap
      (endpointInclusion W x z y L S u hs P R A time oldπ oldθ Q c ⋙
        JTSupportedPathWhiskeredRaw.toOriginal W x z y L S u hs P R A
          time oldπ oldθ Q c)) := by
    change WeakEquivalence
      (nerveMap (endpointInclusion W x z y L S u hs P R A
        time oldπ oldθ Q c) ≫
        nerveMap (JTSupportedPathWhiskeredRaw.toOriginal
          W x z y L S u hs P R A time oldπ oldθ Q c))
    infer_instance
  have hcomm : nerveMap
      (toOldPresentation W x z y L S u hs P R A time oldπ oldθ Q c) ≫
      nerveMap (Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram
        (oldReduced W x z y L P R A time oldπ Q c))) =
      nerveMap (endpointInclusion W x z y L S u hs P R A
        time oldπ oldθ Q c ⋙
        JTSupportedPathWhiskeredRaw.toOriginal W x z y L S u hs P R A
          time oldπ oldθ Q c) := by
    simpa only [nerveFunctor.map_comp] using congrArg nerveMap
      (toOldPresentation_forget W x z y L S u hs P R A
        time oldπ oldθ Q c)
  exact weakEquivalence_of_postcomp_of_fac hcomm

end
end DaggerModels.PartII.JTSupportedPathWhiskeredZeroEvaluation
