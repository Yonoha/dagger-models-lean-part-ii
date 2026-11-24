import DaggerModelsPartII.JTSupportedPathWhiskeredZeroEvaluation
import DaggerModelsPartII.JTWhiskeredMiddleConstantEvaluation
import DaggerModelsPartII.JTNativeTimeProductTargetTransport

/-!
# Whole whiskered path at its constant-middle endpoint

The comparison keeps the full inverse-image endpoint boundary and all
internal necklaces. The constant-middle graph uses the original graph and
time; its native collapse is transported through the identity-component
native isomorphism. The source map is the reindexed complete-pushout map of
`JTReindexedEndpointCoverTransport`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

open CategoryTheory Limits Opposite Simplicial CartesianMonoidalCategory DaggerModels
open MonoidalCategory
open HomotopicalAlgebra
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSupportedPathWhiskeredOneEvaluation

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

private theorem productInterface_inv_app {C : Type} [SmallCategory C]
    (N : C ⥤ NecklaceCode) (time : C ⥤ SimplexCategory)
    {X : SSet.{0}} (U : NecklaceCode) (q : U.toSSet ⟶ X)
    (c : N ⟶ (Functor.const C).obj U) (a : C) :
    (JTGraphCoveredProductInterface.iso N time U q c).inv.app a = 𝟙 _ := rfl

private theorem nativeBoundary_square {C : Type} [SmallCategory C]
    {N M : C ⥤ NecklaceCode} (e : N ≅ M) (time : C ⥤ SimplexCategory) (a : C) :
    (JTNecklaceEndpointCylinder.endpointInclusion (N.obj a) ⊗ₘ
        𝟙 (J.obj (time.obj a))) ≫
      (JTNativeTimeProductTransport.iso e time).hom.app a =
    JTNecklaceEndpointCylinder.endpointInclusion (M.obj a) ⊗ₘ
      𝟙 (J.obj (time.obj a)) := by
  rw [JTNativeTimeProductTransport.hom_app, tensorHom_comp_tensorHom, Category.id_comp,
    JTNecklaceEndpointCylinder.endpointInclusion_natural]

section Family

variable {C : Type} [SmallCategory C] {V : Source} {p q : Vertex V}
variable {P M R : C ⥤ NecklaceCode} {K : C ⥤ SimplexCategory}
variable (Q : NecklacesOver (Raw V) (rawVertex V p) (rawVertex V q))
variable (F : JTVariableMiddleWhiskeredDiagram.Family
  (W := V) (x := p) (y := q) P M R K)
variable (time : C ⥤ SimplexCategory)
variable (c : JTParametrizedTargetFamilies.codes F.labels ⟶ (Functor.const C).obj Q.code)
variable {Y : C ⥤ SSet.{0}}
variable (π : Y ⟶ JTVariableMiddleGraphEvaluation.productDiagram Q F time c)
variable (θ : Y ⟶ K ⋙ J)
variable (H : ∀ a : C, JTWhiskeredGraphRaw.PieceEquations V (F.data a)
  (JTVariableMiddleGraphEvaluation.nativeCoordinate Q F time c π a)
  (θ.app a) (JTVariableMiddleGraphEvaluation.rawTarget Q F c a))

private def familyLift :
    JTVariableMiddleGraphEvaluation.reduced Q F time c π ⟶
      F.labels ⋙ JTTargetCommaPullback.diagram V p q Q :=
  JTVariableMiddleGraphEvaluation.pullbackLift Q F time c π θ H

private theorem familyEvaluation_eq_mapPresentation :
    JTVariableMiddleGraphEvaluation.evaluation Q F time c π θ H =
    JTBoundaryNecklacePresentationCone.mapPresentation
      (JTTargetCommaPullback.diagram V p q Q)
      (JTVariableMiddleGraphEvaluation.reduced Q F time c π) F.labels
      (familyLift Q F time c π θ H) ⋙
      JTTargetCommaExactEvaluation.fromPresentation V p q Q := rfl

private def familyDecorated :
    JTVariableMiddleGraphEvaluation.reduced Q F time c π ⟶ F.labels ⋙ underDiagram V p q :=
  JTGraphCoveredLabelEvaluation.decorated Q F.labels time c π θ

private theorem familyDecorated_cylinder (a : C) :
    (JTGraphCoveredCylinderEquations.inc Q F.labels time c π).app a ≫
      ((familyDecorated Q F time c π θ).app a).right =
    lift (JTVariableMiddleGraphEvaluation.nativeCoordinate Q F time c π a) (θ.app a) ≫
      (JTNecklaceEndpointCylinder.cylinder
        (wedge (P.obj a) (wedge (M.obj a) (R.obj a)))).app (K.obj a) :=
  JTGraphCoveredCylinderEquations.decorated_cylinder Q F.labels time c π θ a

private theorem familyLift_fst (a : C) :
    (familyLift Q F time c π θ H).app a ≫
      JTTargetCommaPullback.fst V p q Q (F.labels.obj a) =
    (familyDecorated Q F time c π θ).app a :=
  JTDecoratedIntervalCylinder.liftFromProjections_fst _ _ _ _ _ _ _

private theorem familyLift_snd (a : C) :
    (familyLift Q F time c π θ H).app a ≫
      JTTargetCommaPullback.snd V p q Q (F.labels.obj a) =
    (JTGraphCoveredLabelEvaluation.nativeLeg Q F.labels time c π).app a :=
  JTDecoratedIntervalCylinder.liftFromProjections_snd _ _ _ _ _ _ _

end Family

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
variable (oldθ : Y ⟶
  JTParametrizedTargetFamilyComparison.degrees L ⋙ J)
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (c : JTParametrizedTargetFamilies.codes
  (JTSupportedPathWhiskeredGraph.oldLabels W x z y L P R A) ⟶
    (Functor.const I).obj Q.code)

private abbrev oldT (a : I) := wedge (P.obj a)
  (wedge ((JTParametrizedTargetFamilies.codes L).obj a) (R.obj a))
private abbrev oldK := JTParametrizedTargetFamilyComparison.degrees L

private abbrev pathIndex := JTSupportedPathChainLabels.Index W z L S u hs
private abbrev pathBase := JTSupportedPathChainLabels.toOriginal W z L S u hs
private abbrev pathLabels := JTSupportedPathWhiskeredGraph.pathLabels
  W x z y L S u hs P R A
private abbrev pathTime := pathBase W z L S u hs ⋙ time
private abbrev pathCollapse := JTSupportedPathWhiskeredRaw.collapse
  W x z y L S u hs P R A Q c
private abbrev pathπ := JTSupportedPathWhiskeredGraph.projectionNew
  W x z y L S u hs P R A time oldπ oldθ
private abbrev pathGraph := JTSupportedPathWhiskeredGraph.graph
  W z L S u hs oldθ
private abbrev constantFamily :=
  JTSupportedPathWhiskeredEndpointLabels.constantFamily W x z y L P R A
private abbrev constantLabels :=
  JTSupportedPathWhiskeredEndpointLabels.constantLabels W x z y L P R A
private abbrev constantCollapse :=
  JTWhiskeredMiddleConstantEvaluation.collapse W x z y L P R A Q c
private abbrev constantπ :=
  JTWhiskeredMiddleConstantEvaluation.projection
    W x z y L P R A time oldπ Q c
private abbrev constantReduced :=
  JTWhiskeredMiddleConstantEvaluation.reduced
    W x z y L P R A time oldπ Q c
private abbrev constantProduct :=
  JTVariableMiddleGraphEvaluation.productDiagram Q
    (constantFamily W x z y L P R A) time
    (constantCollapse W x z y L P R A Q c)
private abbrev constantBoundary := JTGraphCoveredLabelEvaluation.boundary Q
  (constantLabels W x z y L P R A) time
  (constantCollapse W x z y L P R A Q c)
private abbrev pathBoundary := JTGraphCoveredLabelEvaluation.boundary Q
  (pathLabels W x z y L S u hs P R A)
  (pathTime W z L S u hs time)
  (pathCollapse W x z y L S u hs P R A Q c)
private abbrev pathE := Functor.whiskerLeft
  (pathTime W z L S u hs time)
  JTXiEndpointCollapse.cylinderProjection
private abbrev constantE := Functor.whiskerLeft time
  JTXiEndpointCollapse.cylinderProjection

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
      constantProduct W x z y L P R A time Q c :=
  (JTGraphCoveredProductInterface.iso
      (JTParametrizedTargetFamilies.codes
        (pathLabels W x z y L S u hs P R A))
      (pathTime W z L S u hs time) Q.code Q.map
      (pathCollapse W x z y L S u hs P R A Q c)).inv ≫
    eqToHom (rawProductEq W x z y L S u hs P R A time) ≫
    Functor.whiskerLeft (pathBase W z L S u hs)
      (JTWhiskeredMiddleConstantEvaluation.productIso
        W x z y L P R A time Q c).hom

private theorem productReindex_app (p : pathIndex W z L S u hs) :
    ((productReindex W x z y L S u hs P R A time Q c).app p :
        (oldT W z L P R ((pathBase W z L S u hs).obj p)).toSSet ⊗
            J.obj (time.obj ((pathBase W z L S u hs).obj p)) ⟶
          (oldT W z L P R ((pathBase W z L S u hs).obj p)).toSSet ⊗
            J.obj (time.obj ((pathBase W z L S u hs).obj p))) =
      ((JTWhiskeredMiddleConstantEvaluation.productIso
        W x z y L P R A time Q c).hom.app
          ((pathBase W z L S u hs).obj p) :
        (oldT W z L P R ((pathBase W z L S u hs).obj p)).toSSet ⊗
            J.obj (time.obj ((pathBase W z L S u hs).obj p)) ⟶
          (oldT W z L P R ((pathBase W z L S u hs).obj p)).toSSet ⊗
            J.obj (time.obj ((pathBase W z L S u hs).obj p))) := by
  simp only [productReindex, NatTrans.comp_app, Functor.whiskerLeft_app,
    rawProductEq, eqToHom_refl, Category.id_comp,
    productInterface_inv_app]

private theorem graphProduct_square :
    pathπ W x z y L S u hs P R A time oldπ oldθ ≫
      productReindex W x z y L S u hs P R A time Q c =
    JTSupportedPathWhiskeredGraph.toOld W z L S u hs oldθ ≫
      Functor.whiskerLeft (pathBase W z L S u hs)
        (constantπ W x z y L P R A time oldπ Q c) := by
  apply NatTrans.ext
  funext p
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    productReindex_app,
    JTSupportedPathWhiskeredGraph.projectionNew_app]
  exact Category.assoc _ _ _

private def boundaryReindex :
    pathTime W z L S u hs time ⋙ JTXiEndpointCollapse.boundaryCylinder ⟶
    pathBase W z L S u hs ⋙
      (time ⋙ JTXiEndpointCollapse.boundaryCylinder) := 𝟙 _

private theorem boundary_square :
    pathBoundary W x z y L S u hs P R A time Q c ≫
      productReindex W x z y L S u hs P R A time Q c =
    boundaryReindex W z L S u hs time ≫
      Functor.whiskerLeft (pathBase W z L S u hs)
        (constantBoundary W x z y L P R A time Q c) := by
  apply NatTrans.ext
  funext p
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    productReindex_app, boundaryReindex]
  change (JTNecklaceEndpointCylinder.endpointInclusion
      ((JTParametrizedTargetFamilies.codes
        (JTSupportedPathWhiskeredGraph.oldLabels W x z y L P R A)).obj
        ((pathBase W z L S u hs).obj p)) ⊗ₘ
        𝟙 (J.obj (time.obj ((pathBase W z L S u hs).obj p)))) ≫
      (JTWhiskeredMiddleConstantEvaluation.productIso
        W x z y L P R A time Q c).hom.app
          ((pathBase W z L S u hs).obj p) =
    JTNecklaceEndpointCylinder.endpointInclusion
      ((JTParametrizedTargetFamilies.codes
        (constantLabels W x z y L P R A)).obj
        ((pathBase W z L S u hs).obj p)) ⊗ₘ
        𝟙 (J.obj (time.obj ((pathBase W z L S u hs).obj p)))
  rw [JTWhiskeredMiddleConstantEvaluation.productIso]
  simp only [Iso.trans_hom, NatTrans.comp_app,
    JTGraphCoveredProductInterface.iso_hom_app, Category.comp_id]
  exact nativeBoundary_square
    (JTVariableMiddleNativeProjection.nativeIso
      (JTSupportedPathWhiskeredGraph.oldFamily W x z y L P R A)
      (constantFamily W x z y L P R A)) time
    ((pathBase W z L S u hs).obj p)

private theorem endpoint_square (p : pathIndex W z L S u hs) :
    (boundaryReindex W z L S u hs time).app p ≫
      (constantE time).app ((pathBase W z L S u hs).obj p) =
      (pathE W z L S u hs time).app p := by
  rfl

/-- Transport of the complete inverse-image quotient to the literal
constant-middle graph-covered quotient at every path parameter. -/
def sourceChangeAll :
    JTSupportedPathWhiskeredRaw.reduced W x z y L S u hs P R A time
      oldπ oldθ Q c ⟶
    pathBase W z L S u hs ⋙
      constantReduced W x z y L P R A time oldπ Q c :=
  JTReindexedEndpointCoverTransport.sourceChange
    (pathBase W z L S u hs)
    (constantπ W x z y L P R A time oldπ Q c)
    (constantBoundary W x z y L P R A time Q c) (constantE time)
    (pathπ W x z y L S u hs P R A time oldπ oldθ)
    (pathBoundary W x z y L S u hs P R A time Q c)
    (pathE W z L S u hs time)
    (productReindex W x z y L S u hs P R A time Q c)
    (JTSupportedPathWhiskeredGraph.toOld W z L S u hs oldθ)
    (boundaryReindex W z L S u hs time)
    (graphProduct_square W x z y L S u hs P R A time oldπ oldθ Q c).symm
    (boundary_square W x z y L S u hs P R A time Q c)
    (endpoint_square W z L S u hs time)

private abbrev First := JTSupportedPathChainLabels.First W z L S u hs
private abbrev oneSection :=
  JTSupportedPathChainEndpoints.endpointSection W z L S u hs 1
private abbrev original :=
  oneSection W z L S u hs ⋙ pathBase W z L S u hs

/-- Restriction of the complete source transport to the constant-middle
endpoint of the supported path. -/
def sourceChange1 :
    oneSection W z L S u hs ⋙
      JTSupportedPathWhiskeredRaw.reduced W x z y L S u hs P R A time
        oldπ oldθ Q c ⟶
    original W z L S u hs ⋙
      constantReduced W x z y L P R A time oldπ Q c :=
  Functor.whiskerLeft (oneSection W z L S u hs)
    (sourceChangeAll W x z y L S u hs P R A time oldπ oldθ Q c)

private theorem sourceChangeAll_cylinder (p : pathIndex W z L S u hs) :
    (JTGraphCoveredCylinderEquations.inc Q
      (pathLabels W x z y L S u hs P R A)
      (pathTime W z L S u hs time)
      (pathCollapse W x z y L S u hs P R A Q c)
      (pathπ W x z y L S u hs P R A time oldπ oldθ)).app p ≫
        ((sourceChangeAll W x z y L S u hs P R A time oldπ oldθ Q c).app p).right =
    (JTSupportedPathWhiskeredGraph.toOld W z L S u hs oldθ).app p ≫
      (JTGraphCoveredCylinderEquations.inc Q
        (constantLabels W x z y L P R A) time
        (constantCollapse W x z y L P R A Q c)
        (constantπ W x z y L P R A time oldπ Q c)).app
          ((pathBase W z L S u hs).obj p) :=
  JTReindexedEndpointCoverTransport.sourceChange_cylinder
    (pathBase W z L S u hs)
    (constantπ W x z y L P R A time oldπ Q c)
    (constantBoundary W x z y L P R A time Q c) (constantE time)
    (pathπ W x z y L S u hs P R A time oldπ oldθ)
    (pathBoundary W x z y L S u hs P R A time Q c)
    (pathE W z L S u hs time)
    (productReindex W x z y L S u hs P R A time Q c)
    (JTSupportedPathWhiskeredGraph.toOld W z L S u hs oldθ)
    (boundaryReindex W z L S u hs time)
    (graphProduct_square W x z y L S u hs P R A time oldπ oldθ Q c).symm
    (boundary_square W x z y L S u hs P R A time Q c)
    (endpoint_square W z L S u hs time) p

private abbrev pathNative := JTGraphCoveredLabelEvaluation.nativeLeg Q
  (pathLabels W x z y L S u hs P R A)
  (pathTime W z L S u hs time)
  (pathCollapse W x z y L S u hs P R A Q c)
  (pathπ W x z y L S u hs P R A time oldπ oldθ)
private abbrev constantNative := JTGraphCoveredLabelEvaluation.nativeLeg Q
  (constantLabels W x z y L P R A) time
  (constantCollapse W x z y L P R A Q c)
  (constantπ W x z y L P R A time oldπ Q c)

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

private theorem pathNative_square (p : pathIndex W z L S u hs) :
    (pathπ W x z y L S u hs P R A time oldπ oldθ).app p ≫
      fst (wedge (P.obj ((pathBase W z L S u hs).obj p))
        (wedge ((JTParametrizedTargetFamilies.codes L).obj
          ((pathBase W z L S u hs).obj p))
          (R.obj ((pathBase W z L S u hs).obj p)))).toSSet
        (J.obj (time.obj ((pathBase W z L S u hs).obj p))) =
    (JTSupportedPathWhiskeredGraph.toOld W z L S u hs oldθ).app p ≫
      oldπ.app ((pathBase W z L S u hs).obj p) ≫
      fst (wedge (P.obj ((pathBase W z L S u hs).obj p))
        (wedge ((JTParametrizedTargetFamilies.codes L).obj
          ((pathBase W z L S u hs).obj p))
          (R.obj ((pathBase W z L S u hs).obj p)))).toSSet
        (J.obj (time.obj ((pathBase W z L S u hs).obj p))) := by
  rw [JTSupportedPathWhiskeredGraph.projectionNew_app]
  exact Category.assoc _ _ _

private theorem native_square_all (p : pathIndex W z L S u hs) :
    (pathNative W x z y L S u hs P R A time oldπ oldθ Q c).app p =
    (sourceChangeAll W x z y L S u hs P R A time oldπ oldθ Q c).app p ≫
      (constantNative W x z y L P R A time oldπ Q c).app
        ((pathBase W z L S u hs).obj p) := by
  apply Under.UnderMorphism.ext
  apply (pathPushout W x z y L S u hs P R A time oldπ oldθ Q c p).hom_ext
  · change ((JTGraphCoveredCylinderEquations.inc Q
        (pathLabels W x z y L S u hs P R A)
        (pathTime W z L S u hs time)
        (pathCollapse W x z y L S u hs P R A Q c)
        (pathπ W x z y L S u hs P R A time oldπ oldθ)).app p ≫
          ((pathNative W x z y L S u hs P R A time oldπ oldθ Q c).app p).right) =
      ((JTGraphCoveredCylinderEquations.inc Q
        (pathLabels W x z y L S u hs P R A)
        (pathTime W z L S u hs time)
        (pathCollapse W x z y L S u hs P R A Q c)
        (pathπ W x z y L S u hs P R A time oldπ oldθ)).app p ≫
          ((sourceChangeAll W x z y L S u hs P R A time oldπ oldθ Q c).app p).right) ≫
            ((constantNative W x z y L P R A time oldπ Q c).app
              ((pathBase W z L S u hs).obj p)).right
    rw [JTGraphCoveredComparisonEquations.native_cylinder,
      sourceChangeAll_cylinder, Category.assoc,
      JTGraphCoveredComparisonEquations.native_cylinder]
    change (pathπ W x z y L S u hs P R A time oldπ oldθ).app p ≫
        fst _ _ ≫ (c.app ((pathBase W z L S u hs).obj p)).map =
      (JTSupportedPathWhiskeredGraph.toOld W z L S u hs oldθ).app p ≫
        ((oldπ.app ((pathBase W z L S u hs).obj p) ≫
          (JTWhiskeredMiddleConstantEvaluation.productIso
            W x z y L P R A time Q c).hom.app
              ((pathBase W z L S u hs).obj p)) ≫
            fst _ _ ≫ ((constantCollapse W x z y L P R A Q c).app
              ((pathBase W z L S u hs).obj p)).map)
    rw [JTWhiskeredMiddleConstantEvaluation.productIso]
    simp only [Iso.trans_hom, NatTrans.comp_app,
      JTGraphCoveredProductInterface.iso_hom_app, Category.comp_id]
    calc
      _ = (JTSupportedPathWhiskeredGraph.toOld W z L S u hs oldθ).app p ≫
          (oldπ.app ((pathBase W z L S u hs).obj p) ≫ fst _ _ ≫
            (c.app ((pathBase W z L S u hs).obj p)).map) := by
        simpa only [Category.assoc] using
          congrArg (· ≫ (c.app ((pathBase W z L S u hs).obj p)).map)
            (pathNative_square W x z y L S u hs P R A time oldπ oldθ p)
      _ = _ := by
        exact congrArg
          (fun f ↦ (JTSupportedPathWhiskeredGraph.toOld W z L S u hs oldθ).app p ≫ f)
          (JTNativeTimeProductTargetTransport.native_square
            (JTVariableMiddleNativeProjection.nativeIso
              (JTSupportedPathWhiskeredGraph.oldFamily W x z y L P R A)
              (constantFamily W x z y L P R A)) time c
            ((pathBase W z L S u hs).obj p)
            (oldπ.app ((pathBase W z L S u hs).obj p))).symm
  · exact (Under.w ((pathNative W x z y L S u hs P R A time oldπ oldθ Q c).app p)).trans
      (Under.w ((sourceChangeAll W x z y L S u hs P R A time oldπ oldθ Q c).app p ≫
        (constantNative W x z y L P R A time oldπ Q c).app
          ((pathBase W z L S u hs).obj p))).symm


variable (oldRaw : ∀ a : I,
  lift (oldπ.app a ≫ fst (wedge (P.obj a)
      (wedge ((JTParametrizedTargetFamilies.codes L).obj a)
        (R.obj a))).toSSet (J.obj (time.obj a))) (oldθ.app a) ≫
    JTNecklaceLabelRealization.realizedLabel
      (wedge (P.obj a)
        (wedge ((JTParametrizedTargetFamilies.codes L).obj a)
          (R.obj a))).toSSet W
      ((JTParametrizedTargetFamilyComparison.degrees L).obj a)
      (SSet.yonedaEquiv (JTComposedPrismLabels.coefficient
        (JTThreePieceLabelOperators.coefficients
          (JTSupportedPathWhiskeredGraph.oldData W x z y L P R A a)))) =
    (oldπ.app a ≫ fst (wedge (P.obj a)
      (wedge ((JTParametrizedTargetFamilies.codes L).obj a)
        (R.obj a))).toSSet (J.obj (time.obj a))) ≫
      (c.app a).map ≫ Q.map)
variable (oldMiddleQ : ∀ a : I,
  pullback (oldπ.app a ≫ fst (wedge (P.obj a)
      (wedge ((JTParametrizedTargetFamilies.codes L).obj a)
        (R.obj a))).toSSet (J.obj (time.obj a)))
    (tripleRightU (P.obj a)
      ((JTParametrizedTargetFamilies.codes L).obj a) (R.obj a)) ⟶
        J.obj (S.obj a))
variable (oldMiddleFactor : ∀ a : I,
  pullback.fst (oldπ.app a ≫ fst (wedge (P.obj a)
      (wedge ((JTParametrizedTargetFamilies.codes L).obj a)
        (R.obj a))).toSSet (J.obj (time.obj a)))
      (tripleRightU (P.obj a)
        ((JTParametrizedTargetFamilies.codes L).obj a) (R.obj a)) ≫
        oldθ.app a = oldMiddleQ a ≫ J.map (u.app a))

include hs oldRaw oldMiddleQ oldMiddleFactor in
def constantLift :
    constantReduced W x z y L P R A time oldπ Q c ⟶
    constantLabels W x z y L P R A ⋙
      JTTargetCommaPullback.diagram W x y Q :=
  familyLift Q
    (constantFamily W x z y L P R A) time
    (constantCollapse W x z y L P R A Q c)
    (constantπ W x z y L P R A time oldπ Q c) oldθ
    (JTWhiskeredMiddleConstantEvaluation.piecesForEvaluation
      W x z y L S u hs P R A time oldπ oldθ Q c
      oldRaw oldMiddleQ oldMiddleFactor)

include hs oldRaw oldMiddleQ oldMiddleFactor in
theorem constantEvaluation_eq_mapPresentation :
    JTWhiskeredMiddleConstantEvaluation.evaluation
      W x z y L S u hs P R A time oldπ oldθ Q c
      oldRaw oldMiddleQ oldMiddleFactor =
    JTBoundaryNecklacePresentationCone.mapPresentation
      (JTTargetCommaPullback.diagram W x y Q)
      (constantReduced W x z y L P R A time oldπ Q c)
      (constantLabels W x z y L P R A)
      (constantLift W x z y L S u hs P R A time oldπ oldθ Q c
        oldRaw oldMiddleQ oldMiddleFactor) ⋙
      JTTargetCommaExactEvaluation.fromPresentation W x y Q :=
  familyEvaluation_eq_mapPresentation Q
    (constantFamily W x z y L P R A) time
    (constantCollapse W x z y L P R A Q c)
    (constantπ W x z y L P R A time oldπ Q c) oldθ
    (JTWhiskeredMiddleConstantEvaluation.piecesForEvaluation
      W x z y L S u hs P R A time oldπ oldθ Q c
      oldRaw oldMiddleQ oldMiddleFactor)

include oldRaw oldMiddleQ oldMiddleFactor in
private def pathLift (hu : ∀ a : I, Mono (u.app a)) :
    JTSupportedPathWhiskeredRaw.reduced W x z y L S u hs P R A time
      oldπ oldθ Q c ⟶
    pathLabels W x z y L S u hs P R A ⋙
      JTTargetCommaPullback.diagram W x y Q :=
  familyLift Q
    (JTSupportedPathWhiskeredDiagram.variableMiddleFamily
      W x z y L S u hs P R A)
    (pathTime W z L S u hs time)
    (pathCollapse W x z y L S u hs P R A Q c)
    (pathπ W x z y L S u hs P R A time oldπ oldθ)
    (JTSupportedPathWhiskeredGraph.parameter W z L S u hs oldθ)
    (JTSupportedPathWhiskeredRaw.pieceEquations
      W x z y L S u hs P R A time oldπ oldθ Q c
      oldRaw oldMiddleQ oldMiddleFactor hu)

private abbrev proj := OrderedLabelElements.projection W
  (OrderedNecklaceVertexPoints.boundaryPoint W x y)

private theorem oneNative_id (p : First W z L S u hs) :
    ((proj W x y).map
      ((JTSupportedPathWhiskeredEndpointLabels.oneToConstant
        W x z y L S u hs P R A).app p)).1 =
      𝟙 (wedge (P.obj ((original W z L S u hs).obj p))
        (wedge ((JTParametrizedTargetFamilies.codes L).obj
          ((original W z L S u hs).obj p))
          (R.obj ((original W z L S u hs).obj p)))) := by
  have h := congrArg Prod.fst
    (JTSupportedPathWhiskeredEndpointLabels.oneToConstant_projection
      W x z y L S u hs P R A p)
  change _ = _ at h
  rw [h]
  change wedgeMap (𝟙 (P.obj ((original W z L S u hs).obj p)))
      (wedgeMap
        (𝟙 ((JTParametrizedTargetFamilies.codes L).obj
          ((original W z L S u hs).obj p)))
        (𝟙 (R.obj ((original W z L S u hs).obj p)))) =
      𝟙 (wedge (P.obj ((original W z L S u hs).obj p))
        (wedge ((JTParametrizedTargetFamilies.codes L).obj
          ((original W z L S u hs).obj p))
          (R.obj ((original W z L S u hs).obj p))))
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

private theorem oneOrdinal (p : First W z L S u hs) :
    ((proj W x y).map
      ((JTSupportedPathWhiskeredEndpointLabels.oneToConstant
        W x z y L S u hs P R A).app p)).2 =
      (JTSupportedPathChainEndpoints.endpointDegree W z L S u hs 1).app p :=
  congrArg Prod.snd
    (JTSupportedPathWhiskeredEndpointLabels.oneToConstant_projection
      W x z y L S u hs P R A p)

private abbrev pathDecorated := JTGraphCoveredLabelEvaluation.decorated Q
  (pathLabels W x z y L S u hs P R A)
  (pathTime W z L S u hs time)
  (pathCollapse W x z y L S u hs P R A Q c)
  (pathπ W x z y L S u hs P R A time oldπ oldθ)
  (JTSupportedPathWhiskeredGraph.parameter W z L S u hs oldθ)
private abbrev constantDecorated := familyDecorated Q
  (constantFamily W x z y L P R A) time
  (constantCollapse W x z y L P R A Q c)
  (constantπ W x z y L P R A time oldπ Q c) oldθ

private theorem oneParameter_projection (p : First W z L S u hs) :
    (JTSupportedPathWhiskeredGraph.parameter W z L S u hs oldθ).app
        ((oneSection W z L S u hs).obj p) ≫
      J.map ((JTSupportedPathChainEndpoints.endpointDegree W z L S u hs 1).app p) =
    (JTSupportedPathWhiskeredGraph.toOld W z L S u hs oldθ).app
      ((oneSection W z L S u hs).obj p) ≫
      oldθ.app ((original W z L S u hs).obj p) := by
  exact NatTrans.congr_app
    (JTSupportedPathWhiskeredGraph.parameter_old W z L S u hs oldθ)
    ((oneSection W z L S u hs).obj p)

private theorem pathDecorated_cylinder (p : pathIndex W z L S u hs) :
    (JTGraphCoveredCylinderEquations.inc Q
      (pathLabels W x z y L S u hs P R A)
      (pathTime W z L S u hs time)
      (pathCollapse W x z y L S u hs P R A Q c)
      (pathπ W x z y L S u hs P R A time oldπ oldθ)).app p ≫
        ((pathDecorated W x z y L S u hs P R A time oldπ oldθ Q c).app p).right =
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

private theorem decorated_square (p : First W z L S u hs) :
    (pathDecorated W x z y L S u hs P R A time oldπ oldθ Q c).app
        ((oneSection W z L S u hs).obj p) ≫
      (underDiagram W x y).map
        ((JTSupportedPathWhiskeredEndpointLabels.oneToConstant
          W x z y L S u hs P R A).app p) =
    (sourceChange1 W x z y L S u hs P R A time oldπ oldθ Q c).app p ≫
      (constantDecorated W x z y L P R A time oldπ oldθ Q c).app
        ((original W z L S u hs).obj p) := by
  let p₀ := (oneSection W z L S u hs).obj p
  let a := (original W z L S u hs).obj p
  let T := oldT W z L P R a
  let k := (JTSupportedPathChainLabels.ordinals W z L S u hs).obj p₀
  let l := (oldK W z L).obj a
  let f := ((proj W x y).map
    ((JTSupportedPathWhiskeredEndpointLabels.oneToConstant
      W x z y L S u hs P R A).app p)).1
  let α := ((proj W x y).map
    ((JTSupportedPathWhiskeredEndpointLabels.oneToConstant
      W x z y L S u hs P R A).app p)).2
  let h := (pathπ W x z y L S u hs P R A time oldπ oldθ).app p₀ ≫
    fst T.toSSet (J.obj (time.obj a))
  let θ := (JTSupportedPathWhiskeredGraph.parameter W z L S u hs oldθ).app p₀
  let h' := (constantπ W x z y L P R A time oldπ Q c).app a ≫
    fst T.toSSet (J.obj (time.obj a))
  let θ' := oldθ.app a
  let η := (JTSupportedPathWhiskeredGraph.toOld W z L S u hs oldθ).app p₀
  have hf : f = 𝟙 T := oneNative_id W x z y L S u hs P R A p
  have hα : α =
      (JTSupportedPathChainEndpoints.endpointDegree W z L S u hs 1).app p :=
    oneOrdinal W x z y L S u hs P R A p
  have hn : h ≫ f.map = η ≫ h' := by
    rw [hf]
    change h = η ≫ h'
    dsimp only [h']
    rw [JTWhiskeredMiddleConstantEvaluation.projection_app]
    exact pathNative_square W x z y L S u hs P R A time oldπ oldθ p₀
  have hθ : θ ≫ J.map α = η ≫ θ' := by
    rw [hα]
    change θ ≫ J.map
        ((JTSupportedPathChainEndpoints.endpointDegree W z L S u hs 1).app p) =
      η ≫ oldθ.app a
    exact oneParameter_projection W z L S u hs oldθ p
  apply Under.UnderMorphism.ext
  apply (pathPushout W x z y L S u hs P R A time oldπ oldθ Q c p₀).hom_ext
  · change ((JTGraphCoveredCylinderEquations.inc Q
        (pathLabels W x z y L S u hs P R A)
        (pathTime W z L S u hs time)
        (pathCollapse W x z y L S u hs P R A Q c)
        (pathπ W x z y L S u hs P R A time oldπ oldθ)).app p₀ ≫
          ((pathDecorated W x z y L S u hs P R A time oldπ oldθ Q c).app p₀).right) ≫
        ((underDiagram W x y).map
          ((JTSupportedPathWhiskeredEndpointLabels.oneToConstant
            W x z y L S u hs P R A).app p)).right =
      ((JTGraphCoveredCylinderEquations.inc Q
        (pathLabels W x z y L S u hs P R A)
        (pathTime W z L S u hs time)
        (pathCollapse W x z y L S u hs P R A Q c)
        (pathπ W x z y L S u hs P R A time oldπ oldθ)).app p₀ ≫
          ((sourceChangeAll W x z y L S u hs P R A time oldπ oldθ Q c).app p₀).right) ≫
        ((constantDecorated W x z y L P R A time oldπ oldθ Q c).app a).right
    rw [pathDecorated_cylinder, sourceChangeAll_cylinder]
    have hOld :
        (JTGraphCoveredCylinderEquations.inc Q
          (constantLabels W x z y L P R A) time
          (constantCollapse W x z y L P R A Q c)
          (constantπ W x z y L P R A time oldπ Q c)).app
            ((pathBase W z L S u hs).obj p₀) ≫
          ((constantDecorated W x z y L P R A time oldπ oldθ Q c).app a).right =
        lift h' θ' ≫ (JTNecklaceEndpointCylinder.cylinder T).app l := by
      exact familyDecorated_cylinder Q
        (constantFamily W x z y L P R A) time
          (constantCollapse W x z y L P R A Q c)
        (constantπ W x z y L P R A time oldπ Q c)
        oldθ a
    conv_rhs => rw [Category.assoc, hOld]
    change (lift h θ ≫ (JTNecklaceEndpointCylinder.cylinder T).app k) ≫
        (NecklaceCylinderJointDiagram.cylinderUnder.map
          (show (T, k) ⟶ (T, l) from (f, α))).right =
      η ≫ lift h' θ' ≫ (JTNecklaceEndpointCylinder.cylinder T).app l
    exact JTGraphCoveredComparisonEquations.graph_cylinder_map
      f α h θ h' θ' η hn hθ
  · exact (Under.w ((pathDecorated W x z y L S u hs P R A time oldπ oldθ Q c).app p₀ ≫
      (underDiagram W x y).map
        ((JTSupportedPathWhiskeredEndpointLabels.oneToConstant
          W x z y L S u hs P R A).app p))).trans
      (Under.w ((sourceChange1 W x z y L S u hs P R A time oldπ oldθ Q c).app p ≫
        (constantDecorated W x z y L P R A time oldπ oldθ Q c).app a)).symm

include oldRaw oldMiddleQ oldMiddleFactor in
/-- Exact fixed-`Q` square at time one, including both the decorated and
native target legs of every internal-necklace presentation. -/
theorem fixedTarget_square (hu : ∀ a : I, Mono (u.app a))
    (p : First W z L S u hs) :
    (pathLift W x z y L S u hs P R A time oldπ oldθ Q c
      oldRaw oldMiddleQ oldMiddleFactor hu).app
        ((oneSection W z L S u hs).obj p) ≫
      (JTTargetCommaPullback.diagram W x y Q).map
        ((JTSupportedPathWhiskeredEndpointLabels.oneToConstant
          W x z y L S u hs P R A).app p) =
    (sourceChange1 W x z y L S u hs P R A time oldπ oldθ Q c).app p ≫
      (constantLift W x z y L S u hs P R A time oldπ oldθ Q c
        oldRaw oldMiddleQ oldMiddleFactor).app
        ((original W z L S u hs).obj p) := by
  exact JTGraphCoveredComparisonEquations.fixedTarget_square Q
    ((JTSupportedPathWhiskeredEndpointLabels.oneToConstant
      W x z y L S u hs P R A).app p)
    ((sourceChange1 W x z y L S u hs P R A time oldπ oldθ Q c).app p)
    ((pathLift W x z y L S u hs P R A time oldπ oldθ Q c
      oldRaw oldMiddleQ oldMiddleFactor hu).app
        ((oneSection W z L S u hs).obj p))
    ((constantLift W x z y L S u hs P R A time oldπ oldθ Q c
        oldRaw oldMiddleQ oldMiddleFactor).app
      ((original W z L S u hs).obj p))
    (familyLift_fst _ _ _ _ _ _ _ _)
    (familyLift_fst _ _ _ _ _ _ _ _)
    (familyLift_snd _ _ _ _ _ _ _ _)
    (familyLift_snd _ _ _ _ _ _ _ _)
    (decorated_square W x z y L S u hs P R A time oldπ oldθ Q c p)
    (native_square_all W x z y L S u hs P R A time oldπ oldθ Q c
      ((oneSection W z L S u hs).obj p))

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
def oneComparison (hu : ∀ a : I, Mono (u.app a)) :=
  JTBoundaryNecklaceTwoReindexComparison.comparison
    (E := JTTargetCommaPullback.diagram W x y Q)
    (F := JTSupportedPathWhiskeredRaw.reduced W x z y L S u hs P R A
      time oldπ oldθ Q c)
    (L := pathLabels W x z y L S u hs P R A)
    (p := pathLift W x z y L S u hs P R A time oldπ oldθ Q c
      oldRaw oldMiddleQ oldMiddleFactor hu)
    (G := oneSection W z L S u hs)
    (F' := constantReduced W x z y L P R A time oldπ Q c)
    (M := constantLabels W x z y L P R A)
    (q := constantLift W x z y L S u hs P R A time oldπ oldθ Q c
      oldRaw oldMiddleQ oldMiddleFactor)
    (G' := original W z L S u hs)
    (s := sourceChange1 W x z y L S u hs P R A time oldπ oldθ Q c)
    (r := JTSupportedPathWhiskeredEndpointLabels.oneToConstant
      W x z y L S u hs P R A)
    (h := fixedTarget_square W x z y L S u hs P R A time
      oldπ oldθ Q c oldRaw oldMiddleQ oldMiddleFactor hu)
    (JTTargetCommaExactEvaluation.fromPresentation W x y Q)

/-- Full internal-necklace presentation on the time-one endpoint face. -/
abbrev endpointPresentation := BoundaryNecklaceComma.Presentation
  (oneSection W z L S u hs ⋙
    JTSupportedPathWhiskeredRaw.reduced W x z y L S u hs P R A
      time oldπ oldθ Q c)

/-- Insert the time-one endpoint presentation into the complete path presentation. -/
abbrev endpointInclusion : endpointPresentation W x z y L S u hs P R A
    time oldπ oldθ Q c ⥤
    BoundaryNecklaceComma.Presentation
      (JTSupportedPathWhiskeredRaw.reduced W x z y L S u hs P R A
        time oldπ oldθ Q c) :=
  Grothendieck.pre (BoundaryNecklaceComma.fiberDiagram
    (JTSupportedPathWhiskeredRaw.reduced W x z y L S u hs P R A
      time oldπ oldθ Q c)) (oneSection W z L S u hs)

include oldRaw oldMiddleQ oldMiddleFactor in
/-- Exact time-one evaluation of every internal necklace in fixed `Q`. -/
def endpointEvaluation (hu : ∀ a : I, Mono (u.app a)) :
    endpointPresentation W x z y L S u hs P R A time oldπ oldθ Q c ⥤
      JTGraphFactoredPresentation.TargetComma Q :=
  endpointInclusion W x z y L S u hs P R A time oldπ oldθ Q c ⋙
    JTSupportedPathWhiskeredRaw.evaluation W x z y L S u hs P R A
      time oldπ oldθ Q c oldRaw oldMiddleQ oldMiddleFactor hu

/-- Map the full time-one endpoint presentation to the constant-middle
graph-covered presentation, with its entire inverse-image boundary. -/
def toConstantPresentation :
    endpointPresentation W x z y L S u hs P R A time oldπ oldθ Q c ⥤
    BoundaryNecklaceComma.Presentation
      (constantReduced W x z y L P R A time oldπ Q c) :=
  Grothendieck.map (Functor.whiskerRight
    (sourceChange1 W x z y L S u hs P R A time oldπ oldθ Q c)
    BoundaryNecklaceComma.diagram) ⋙
  Grothendieck.pre (BoundaryNecklaceComma.fiberDiagram
    (constantReduced W x z y L P R A time oldπ Q c))
    (original W z L S u hs)

include oldRaw oldMiddleQ oldMiddleFactor in
/-- Typed comparison from the exact time-one endpoint evaluation to the constant-middle
evaluation after transport of every internal necklace. -/
def evaluationComparison (hu : ∀ a : I, Mono (u.app a)) :
    endpointEvaluation W x z y L S u hs P R A time oldπ oldθ Q c
      oldRaw oldMiddleQ oldMiddleFactor hu ⟶
    toConstantPresentation W x z y L S u hs P R A time oldπ oldθ Q c ⋙
      JTWhiskeredMiddleConstantEvaluation.evaluation
        W x z y L S u hs P R A time oldπ oldθ Q c
        oldRaw oldMiddleQ oldMiddleFactor := by
  rw [endpointEvaluation, pathEvaluation_eq_mapPresentation
    W x z y L S u hs P R A time oldπ oldθ Q c
      oldRaw oldMiddleQ oldMiddleFactor hu]
  rw [constantEvaluation_eq_mapPresentation
    W x z y L S u hs P R A time oldπ oldθ Q c
      oldRaw oldMiddleQ oldMiddleFactor]
  exact oneComparison W x z y L S u hs P R A time oldπ oldθ Q c
    oldRaw oldMiddleQ oldMiddleFactor hu

/-- The time-one endpoint inclusion is weak whenever the original whole graph
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
      W z L S u hs 1

/-- The constant-middle presentation forgets to the same original index reached by the
time-one endpoint presentation. -/
private theorem toConstantPresentation_forget :
    toConstantPresentation W x z y L S u hs P R A time oldπ oldθ Q c ⋙
      Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram
        (constantReduced W x z y L P R A time oldπ Q c)) =
    endpointInclusion W x z y L S u hs P R A time oldπ oldθ Q c ⋙
      JTSupportedPathWhiskeredRaw.toOriginal W x z y L S u hs P R A
        time oldπ oldθ Q c := rfl

/-- Weak equivalence of the complete constant-middle presentation comparison. Its
proof only uses weak projections to the common original index. -/
theorem toConstantPresentation_weak
    (hu : ∀ a : I, Mono (u.app a))
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hp : ∀ a : I,
      0 < ((JTParametrizedTargetFamilies.codes L).obj a).len)
    (hπ : ∀ a : I, trivialFibrations SSet.{0} (oldπ.app a)) :
    WeakEquivalence (nerveMap
      (toConstantPresentation W x z y L S u hs P R A time oldπ oldθ Q c)) := by
  letI : WeakEquivalence (nerveMap
      (Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram
        (constantReduced W x z y L P R A time oldπ Q c)))) := by
    exact JTWhiskeredMiddleConstantEvaluation.toOriginal_weak
      W x z y L P R A time oldπ Q c hπ
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
      (toConstantPresentation W x z y L S u hs P R A time oldπ oldθ Q c) ≫
      nerveMap (Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram
        (constantReduced W x z y L P R A time oldπ Q c))) =
      nerveMap (endpointInclusion W x z y L S u hs P R A
        time oldπ oldθ Q c ⋙
        JTSupportedPathWhiskeredRaw.toOriginal W x z y L S u hs P R A
          time oldπ oldθ Q c) := by
    simpa only [nerveFunctor.map_comp] using congrArg nerveMap
      (toConstantPresentation_forget W x z y L S u hs P R A
        time oldπ oldθ Q c)
  exact weakEquivalence_of_postcomp_of_fac hcomm

end
end DaggerModels.PartII.JTSupportedPathWhiskeredOneEvaluation
