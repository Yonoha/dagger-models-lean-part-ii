import DaggerModelsPartII.JTRawOrdinaryAdjoint
import DaggerModelsPartII.JTRawUnitCylinderCalibration
import DaggerModelsPartII.OrderedSimplexEndpointFiber
import DaggerModelsPartII.JTNecklaceEndpointCylinder
import DaggerModelsPartII.JTNecklaceLabelRealization
import DaggerModelsPartII.JTProjectiveRealizationMappingWeak
import DaggerModelsPartII.JTGtildeGeneratorFiberCalibration

/-!
# The actual native single-edge ordered label and the original raw strict fiber

The one-bead inclusion is an isomorphism for `single 1` in every source
diagram. We transport its ordered pullback along the original ambient
simplex fiber isomorphism and evaluate the actual free-dagger-unit label.
No fibrancy or weak equivalence hypothesis is used.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTRawSingleOrderedLabelIso

open OrderedNecklaceLabelDiagram OrderedNecklaceVertexPoints
open OrderedSimplexEndpointFiber JTProjectiveOrderedFiberComparison
open JTRealizedLabelEndpoints JTNecklaceEndpointCylinder
open ReversalDiscreteFreeColimits JTReversalInput
open JTRawFreeInnerComparison JTRawOrdinaryAdjoint
open JTRawUnitCylinderCalibration

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev F := discreteFree.{0}
private abbrev T := single 1

private theorem singleRestriction_eq (W : Source) :
    restriction W T = diagramMappingPrecomp (F.map (singleIso 1).hom) W := by
  rw [singleIso_hom]
  rfl

/-- The raw chosen-fiber action and the strict fiber action calibrated
below retain the exact same strict-to-chosen inclusion triangle. -/
theorem rawChosenFiberMapAtP_inclusion (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj
      (op ⦋0⦌)) :
    ChosenHomotopyFiberTriangle.inclusion (endpointArrow W)
        (point W (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
          (JTProjectiveOrderedFiberComparison.targetVertices W x y).2) ≫
      rawChosenFiberMapAtP W x y =
    rawStrictFiberMapAtP W x y ≫
      ChosenHomotopyFiberTriangle.inclusion
        (JTRightAdjointOrderedFiber.ordinaryEndpointArrow
          (rawTarget W).toSSet)
        (JTRightAdjointOrderedFiber.ordinaryEndpointPoint (rawTarget W)
          ((ell W).hom.app (op ⦋0⦌)
            (JTGtildeOrderedFiberAction.targetVertices W x y).1)
          ((ell W).hom.app (op ⦋0⦌)
            (JTGtildeOrderedFiberAction.targetVertices W x y).2)) := by
  exact ChosenHomotopyFiberFunctor.inclusion_chosenMap
    (endpointArrow W)
    (JTRightAdjointOrderedFiber.ordinaryEndpointArrow (rawTarget W).toSSet)
    (gRawRow W ⦋1⦌) (gRawBase W) (gRawArrow_square W)
    (point W (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
      (JTProjectiveOrderedFiberComparison.targetVertices W x y).2)
    (JTRightAdjointOrderedFiber.ordinaryEndpointPoint (rawTarget W)
      ((ell W).hom.app (op ⦋0⦌)
        (JTGtildeOrderedFiberAction.targetVertices W x y).1)
      ((ell W).hom.app (op ⦋0⦌)
        (JTGtildeOrderedFiberAction.targetVertices W x y).2))
    (rawPoint_square_at_p W x y)

/-- The actual fixed-code restriction is an isomorphism at the native
single edge, for every `W`, with no Segal fibrancy hypothesis. -/
private def singleRestriction_isIso (W : Source) :
    IsIso (restriction W T) := by
  have h : IsIso ((diagramMappingSource W).map
      (F.map (singleIso 1).hom).op) := inferInstance
  rw [singleRestriction_eq]
  exact h

private noncomputable instance (W : Source) : IsIso (restriction W T) :=
  singleRestriction_isIso W

/-- Base change of that same restriction along any ordered boundary
point is an isomorphism of the literal ordered label pullbacks. -/
def singleOrderedRestrictionIso (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W) :
    (orderedSimplexLabels W b).obj (op T) ≅
      (orderedNecklaceLabels W b).obj (op T) := by
  letI : IsIso (restriction W T) := singleRestriction_isIso W
  letI : IsIso ((restrictionNatural W).app (op T)) := by
    change IsIso (restriction W T)
    infer_instance
  have h : IsIso ((orderedRestriction W b).app (op T)) := by
    dsimp only [orderedRestriction]
    infer_instance
  exact asIso ((orderedRestriction W b).app (op T))

theorem singleOrderedRestrictionIso_hom (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W) :
    (singleOrderedRestrictionIso W b).hom =
      (orderedRestriction W b).app (op T) := rfl

/-- The map on ordered labels has the actual first projection
`restriction W (single 1)`, with no abstract isomorphism evaluation. -/
theorem singleOrderedRestriction_fst (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W) :
    (orderedRestriction W b).app (op T) ≫
        pullback.fst ((necklaceBoundaryRestriction W).app (op T)) b =
      pullback.fst ((simplexBoundaryRestriction W).app (op T)) b ≫
        restriction W T := by
  simp only [orderedRestriction, restrictionNatural, pullback.map,
    pullback.lift_fst]

/-- The native single-edge ordered label is the original raw strict
endpoint fiber, through the actual ordered-restriction isomorphism. -/
def nativeSingleFiberIso (W : Source)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    (orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T) ≅
      pullback (endpointArrow W) (point W x y) :=
  (singleOrderedRestrictionIso W (boundaryPoint W x y)).symm ≪≫
    orderedSingleFiberIso W x y

/-- The inverse ordered restriction transports the total label
projection to the original one-row coefficient without reversing
the two endpoint vertices. -/
theorem nativeSingleFiberIso_fst (W : Source)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    (nativeSingleFiberIso W x y).hom ≫
        pullback.fst (endpointArrow W) (point W x y) =
      pullback.fst ((necklaceBoundaryRestriction W).app (op T))
          (boundaryPoint W x y) ≫
        inv (restriction W T) ≫ (freeSimplexRowIso W 1).hom := by
  let e := singleOrderedRestrictionIso W (boundaryPoint W x y)
  have hf := singleOrderedRestriction_fst W (boundaryPoint W x y)
  change e.hom ≫
      pullback.fst ((necklaceBoundaryRestriction W).app (op T))
        (boundaryPoint W x y) =
    pullback.fst ((simplexBoundaryRestriction W).app (op T))
        (boundaryPoint W x y) ≫ restriction W T at hf
  have hfi : e.inv ≫
      pullback.fst ((simplexBoundaryRestriction W).app (op T))
        (boundaryPoint W x y) =
      pullback.fst ((necklaceBoundaryRestriction W).app (op T))
        (boundaryPoint W x y) ≫ inv (restriction W T) := by
    apply (IsIso.eq_comp_inv (restriction W T)).2
    rw [Category.assoc, ← hf, Iso.inv_hom_id_assoc]
  change e.inv ≫ (orderedSingleFiberIso W x y).hom ≫
      pullback.fst (endpointArrow W) (point W x y) = _
  calc
    _ = (e.inv ≫ pullback.fst
          ((simplexBoundaryRestriction W).app (op T))
          (boundaryPoint W x y)) ≫ (freeSimplexRowIso W 1).hom := by
      rw [Category.assoc, orderedSingleFiberIso_fst,
        ← Category.assoc]
    _ = _ := by rw [hfi, Category.assoc]

/-- The actual top bead of the native `single 1`, specified by the
canonical one-bead isomorphism rather than by an arbitrary lift. -/
def nativeTop : T.toSSet.obj (op ⦋1⦌) :=
  (singleIso 1).inv.app (op ⦋1⦌)
    (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌))

theorem nativeTop_identity :
    (singleIso 1).hom.app (op ⦋1⦌) nativeTop =
      SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌) := by
  exact congrFun (Iso.inv_hom_id_app (singleIso 1) (op ⦋1⦌)) _

theorem nativeTop_yoneda :
    SSet.yonedaEquiv.symm nativeTop = (singleIso 1).inv := by
  apply SSet.yonedaEquiv.injective
  change nativeTop =
    (singleIso 1).inv.app (op ⦋1⦌)
      (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌))
  rfl

/-- The literal identity parameter simplex, kept in the original
inner degree `k`. -/
def parameterIdentity (k : SimplexCategory) :
    (SSet.stdSimplex.obj k).obj (op k) :=
  SSet.stdSimplex.objEquiv.symm (𝟙 k)

/-- Enriched Yoneda evaluates the original free-simplex row iso on
the actual free-dagger unit of the identity one-simplex. -/
theorem freeSimplexRowIso_on_unit (W : Source) (k : SimplexCategory)
    (η : (diagramMappingSpace (F.obj (Δ[1] : SSet.{0})) W).obj (op k)) :
    ((freeSimplexRowIso W 1).hom.app (op k)) η =
      (η.app (op (ReverseSimplex.inclusion.obj ⦋1⦌))).app (op k)
        (((freeDaggerAdjunction.unit.app (Δ[1] : SSet.{0})).app
          (op ⦋1⦌) (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌))),
          parameterIdentity k) := by
  let e := SegalRepresentables.freeSimplexRepresentable 1
  have he := ActualUnitNativeComparison.freeSimplexRepresentable_unit_id 1
    (op k)
  have hgen :
      ((e.inv.app (op (ReverseSimplex.inclusion.obj ⦋1⦌))).app (op k))
          (ULift.up (𝟙 (ReverseSimplex.inclusion.obj ⦋1⦌))) =
        (freeDaggerAdjunction.unit.app (Δ[1] : SSet.{0})).app
          (op ⦋1⦌) (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)) := by
    calc
      _ = ((e.inv.app (op (ReverseSimplex.inclusion.obj ⦋1⦌))).app
          (op k))
            (((e.hom.app (op (ReverseSimplex.inclusion.obj ⦋1⦌))).app
              (op k))
                ((freeDaggerAdjunction.unit.app (Δ[1] : SSet.{0})).app
                  (op ⦋1⦌)
                  (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)))) :=
          congrArg
            (fun t => ((e.inv.app
              (op (ReverseSimplex.inclusion.obj ⦋1⦌))).app (op k)) t)
            he.symm
      _ = _ := congrFun
        (NatTrans.congr_app
          (NatTrans.congr_app e.hom_inv_id
            (op (ReverseSimplex.inclusion.obj ⦋1⦌))) (op k)) _
  change (η.app (op (ReverseSimplex.inclusion.obj ⦋1⦌))).app (op k)
      (((e.inv.app (op (ReverseSimplex.inclusion.obj ⦋1⦌))).app (op k))
        (ULift.up (𝟙 (ReverseSimplex.inclusion.obj ⦋1⦌))),
        parameterIdentity k) = _
  rw [hgen]

/-- Restricting the ambient single-simplex label along the actual
native inclusion evaluates on the native top bead exactly as the
ambient label evaluates on the identity edge. -/
theorem restriction_single_on_unit (W : Source) (k : SimplexCategory)
    (η : (diagramMappingSpace (F.obj (Δ[1] : SSet.{0})) W).obj (op k)) :
    (((restriction W T).app (op k) η).app
      (op (ReverseSimplex.inclusion.obj ⦋1⦌))).app (op k)
        (((freeDaggerAdjunction.unit.app T.toSSet).app (op ⦋1⦌)
          nativeTop), parameterIdentity k) =
      (η.app (op (ReverseSimplex.inclusion.obj ⦋1⦌))).app (op k)
        (((freeDaggerAdjunction.unit.app (Δ[1] : SSet.{0})).app
          (op ⦋1⦌)
          (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌))),
          parameterIdentity k) := by
  have hu := congrFun
    (NatTrans.congr_app
      (freeDaggerAdjunction.unit.naturality (singleIso 1).hom).symm
      (op ⦋1⦌)) nativeTop
  have hu' :
      (((F.map (singleIso 1).hom).app
        (op (ReverseSimplex.inclusion.obj ⦋1⦌))).app (op k))
          ((freeDaggerAdjunction.unit.app T.toSSet).app (op ⦋1⦌)
            nativeTop) =
        (freeDaggerAdjunction.unit.app (Δ[1] : SSet.{0})).app
          (op ⦋1⦌)
          (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)) := by
    change ((DaggerSSet.forget.map (freeDagger.map (singleIso 1).hom)).app
      (op ⦋1⦌))
        ((freeDaggerAdjunction.unit.app T.toSSet).app (op ⦋1⦌)
          nativeTop) =
      (freeDaggerAdjunction.unit.app (Δ[1] : SSet.{0})).app
        (op ⦋1⦌) ((singleIso 1).hom.app (op ⦋1⦌) nativeTop) at hu
    simpa only [nativeTop_identity] using hu
  rw [singleRestriction_eq]
  change (η.app (op (ReverseSimplex.inclusion.obj ⦋1⦌))).app (op k)
      (((F.map (singleIso 1).hom).app
        (op (ReverseSimplex.inclusion.obj ⦋1⦌))).app (op k)
          ((freeDaggerAdjunction.unit.app T.toSSet).app (op ⦋1⦌)
            nativeTop), parameterIdentity k) = _
  rw [hu']

/-- The native one-bead label obtained from an actual simplex of
the original raw strict endpoint fiber. -/
def nativeLabelOfRawFiber (W : Source)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
    (k : SimplexCategory)
    (z : (pullback (endpointArrow W) (point W x y)).obj (op k)) :
    ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj
      (op k) :=
  (nativeSingleFiberIso W x y).inv.app (op k) z

/-- The actual native label coefficient at its canonical top bead
and identity parameter is the SAME original one-row coefficient. -/
theorem nativeLabelOfRawFiber_coefficient (W : Source)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
    (k : SimplexCategory)
    (z : (pullback (endpointArrow W) (point W x y)).obj (op k)) :
    (((orderedLabel W x y T k (nativeLabelOfRawFiber W x y k z)).app
        (op (ReverseSimplex.inclusion.obj ⦋1⦌))).app (op k)
          (((freeDaggerAdjunction.unit.app T.toSSet).app (op ⦋1⦌)
            nativeTop), parameterIdentity k)) =
      ((pullback.fst (endpointArrow W) (point W x y)).app (op k)) z := by
  let b := boundaryPoint W x y
  let e := singleOrderedRestrictionIso W b
  let d := orderedSingleFiberIso W x y
  let zAmbient := d.inv.app (op k) z
  let ηAmbient :=
    (pullback.fst ((simplexBoundaryRestriction W).app (op T)) b).app
      (op k) zAmbient
  have hz : nativeLabelOfRawFiber W x y k z =
      e.hom.app (op k) zAmbient := rfl
  have hη : orderedLabel W x y T k (nativeLabelOfRawFiber W x y k z) =
      (restriction W T).app (op k) ηAmbient := by
    rw [hz]
    exact congrFun
      (NatTrans.congr_app (singleOrderedRestriction_fst W b) (op k))
        zAmbient
  have hr := congrFun
    (NatTrans.congr_app (orderedSingleFiberIso_fst W x y) (op k))
      zAmbient
  have hr' : ((freeSimplexRowIso W 1).hom.app (op k)) ηAmbient =
      ((pullback.fst (endpointArrow W) (point W x y)).app (op k)) z := by
    change ((pullback.fst (endpointArrow W) (point W x y)).app (op k))
        (d.hom.app (op k) zAmbient) =
      ((freeSimplexRowIso W 1).hom.app (op k)) ηAmbient at hr
    have hd : d.hom.app (op k) zAmbient = z :=
      congrFun (Iso.inv_hom_id_app d (op k)) z
    rw [hd] at hr
    exact hr.symm
  calc
    _ = (((restriction W T).app (op k) ηAmbient).app
          (op (ReverseSimplex.inclusion.obj ⦋1⦌))).app (op k)
            (((freeDaggerAdjunction.unit.app T.toSSet).app (op ⦋1⦌)
              nativeTop), parameterIdentity k) := by rw [hη]
    _ = (ηAmbient.app (op (ReverseSimplex.inclusion.obj ⦋1⦌))).app
          (op k)
            (((freeDaggerAdjunction.unit.app (Δ[1] : SSet.{0})).app
              (op ⦋1⦌)
              (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌))),
              parameterIdentity k) :=
      restriction_single_on_unit W k ηAmbient
    _ = ((freeSimplexRowIso W 1).hom.app (op k)) ηAmbient :=
      (freeSimplexRowIso_on_unit W k ηAmbient).symm
    _ = ((pullback.fst (endpointArrow W) (point W x y)).app
          (op k)) z := hr'

/-- At the two ACTUAL projective-image vertices, the descended native
single-edge cylinder and the raw transpose strict-fiber CE interval
leg are the same simplex after the original raw free-inner unit. -/
theorem same_simplex_rawCE_interval (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj
      (op ⦋0⦌))
    (k : SimplexCategory)
    (z : (pullback (endpointArrow W)
      (point W (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
        (JTProjectiveOrderedFiberComparison.targetVertices W x y).2)).obj
          (op k)) :
    let a := JTProjectiveOrderedFiberComparison.targetVertices W x y
    let u := (ell W).hom.app (op ⦋0⦌)
      (JTGtildeOrderedFiberAction.targetVertices W x y).1
    let v := (ell W).hom.app (op ⦋0⦌)
      (JTGtildeOrderedFiberAction.targetVertices W x y).2
    let f := ((JTCEOrdinaryFiber.originalFiberCEIso (rawTarget W) u v).hom.app
      (op k)) ((rawStrictFiberMapAtP W x y).app (op k) z)
    let zNative := nativeLabelOfRawFiber W a.1 a.2 k z
    ((SSet.yonedaEquiv.symm nativeTop ⊗ₘ
        𝟙 (GroupoidSimplex.parameter.obj k)) ≫
      (cylinder T).app k ≫ descend W a.1 a.2 T k zNative) ≫
      (rawG W).hom = JTXiEndpointCollapse.CE_interval.app k ≫ f.right := by
  dsimp only
  let a := JTProjectiveOrderedFiberComparison.targetVertices W x y
  let zNative := nativeLabelOfRawFiber W a.1 a.2 k z
  let cNative :=
    (((orderedLabel W a.1 a.2 T k zNative).app
      (op (ReverseSimplex.inclusion.obj ⦋1⦌))).app (op k)
        (((freeDaggerAdjunction.unit.app T.toSSet).app (op ⦋1⦌)
          nativeTop), parameterIdentity k))
  have hd := singleDescend_generator W a.1 a.2 k ⦋1⦌ k
    zNative nativeTop (parameterIdentity k)
  have hd' :
      (SSet.yonedaEquiv.symm nativeTop ⊗ₘ
          𝟙 (GroupoidSimplex.parameter.obj k)) ≫
        (cylinder T).app k ≫ descend W a.1 a.2 T k zNative =
      JTRealizationGenerators.generator (ordinaryInput.obj W) (⦋1⦌, k)
        cNative := by
    simp only [parameterIdentity, Equiv.apply_symm_apply] at hd
    rw [GroupoidSimplex.parameter.map_id] at hd
    exact hd
  have hc := nativeLabelOfRawFiber_coefficient W a.1 a.2 k z
  have hc' : cNative = rawOneCoefficientAtP W x y k z := by
    simpa only [cNative, rawOneCoefficientAtP, a] using hc
  have hr := rawStrictFiberCE_interval W x y k z
  calc
    _ = JTRealizationGenerators.generator (ordinaryInput.obj W)
          (⦋1⦌, k) cNative ≫ (rawG W).hom := by
      simpa only [Category.assoc] using
        congrArg (fun h => h ≫ (rawG W).hom) hd'
    _ = JTRealizationGenerators.generator (ordinaryInput.obj W)
          (⦋1⦌, k) (rawOneCoefficientAtP W x y k z) ≫
            (rawG W).hom := by rw [hc']
    _ = JTXiEndpointCollapse.CE_interval.app k ≫
          (((JTCEOrdinaryFiber.originalFiberCEIso (rawTarget W)
            ((ell W).hom.app (op ⦋0⦌)
              (JTGtildeOrderedFiberAction.targetVertices W x y).1)
            ((ell W).hom.app (op ⦋0⦌)
              (JTGtildeOrderedFiberAction.targetVertices W x y).2)).hom.app
                (op k)) ((rawStrictFiberMapAtP W x y).app (op k) z)).right :=
      hr.symm

/-- The raw free-inner unit carries the original raw zero generator
at the actual projective image to the original chosen target vertex
followed by the canonical comparison `ell`. -/
theorem rawG_zeroGenerator_at_p (W : Source)
    (x : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj
      (op ⦋0⦌)) :
    (rawG W).hom.app (op ⦋0⦌)
        (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W
          ((pRow W ⦋0⦌).app (op ⦋0⦌) x)) =
      (ell W).hom.app (op ⦋0⦌)
        (JTGtildeOrderedFiberAction.targetVertex W
          ((JTGtildeOrderedFiberAction.gRow W ⦋0⦌).app
            (op ⦋0⦌) x)) := by
  let z := JTGtildeGeneratorFiberCalibration.zeroGeneratorVertex W x
  have hs : JTProjectiveRealizationMappingWeak.realizedP W ≫
      (rawG W).hom =
      (JTStrictificationCoefficients.chosenG W).hom ≫ (ell W).hom := by
    rw [← underlying_projective_map W]
    exact (underlying_square W).symm
  calc
    _ = (rawG W).hom.app (op ⦋0⦌)
          ((JTProjectiveRealizationMappingWeak.realizedP W).app
            (op ⦋0⦌) z) := by
      rw [JTProjectiveRealizationMappingWeak.realizedP_zeroGeneratorVertex]
    _ = (JTProjectiveRealizationMappingWeak.realizedP W ≫
          (rawG W).hom).app (op ⦋0⦌) z := rfl
    _ = ((JTStrictificationCoefficients.chosenG W).hom ≫
          (ell W).hom).app (op ⦋0⦌) z := by rw [hs]
    _ = (ell W).hom.app (op ⦋0⦌)
          ((JTStrictificationCoefficients.chosenG W).hom.app (op ⦋0⦌) z) := rfl
    _ = _ := by
      have hz :=
        JTGtildeGeneratorFiberCalibration.chosenG_zeroGeneratorVertex W x
      change ((JTStrictificationCoefficients.chosenG W).hom.app
        (op ⦋0⦌))
        (JTGtildeGeneratorFiberCalibration.zeroGeneratorVertex W x) =
          JTGtildeOrderedFiberAction.targetVertex W
            ((JTGtildeOrderedFiberAction.gRow W ⦋0⦌).app
              (op ⦋0⦌) x) at hz
      exact congrArg ((ell W).hom.app (op ⦋0⦌)) hz

/-- The two complete ordered boundary legs agree after the actual raw
unit, at the unchanged `p`-image endpoints. -/
theorem rawBoundary_image_at_p (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj
      (op ⦋0⦌)) :
    let a := JTProjectiveOrderedFiberComparison.targetVertices W x y
    let u := (ell W).hom.app (op ⦋0⦌)
      (JTGtildeOrderedFiberAction.targetVertices W x y).1
    let v := (ell W).hom.app (op ⦋0⦌)
      (JTGtildeOrderedFiberAction.targetVertices W x y).2
    rawBoundary W a.1 a.2 ≫ (rawG W).hom =
      JTUnderlyingOrderedFibers.ordinaryBoundary (rawTarget W) u v := by
  dsimp only
  apply SSet.boundary₁.hom_ext
  · rw [← Category.assoc]
    change (SSet.boundary₁.ι₀ ≫ SSet.boundary₁.desc
        (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W
          (JTProjectiveOrderedFiberComparison.targetVertices W x y).1)
        (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W
          (JTProjectiveOrderedFiberComparison.targetVertices W x y).2)) ≫
          (rawG W).hom =
      SSet.boundary₁.ι₀ ≫ SSet.boundary₁.desc
        ((ell W).hom.app (op ⦋0⦌)
          (JTGtildeOrderedFiberAction.targetVertices W x y).1)
        ((ell W).hom.app (op ⦋0⦌)
          (JTGtildeOrderedFiberAction.targetVertices W x y).2)
    simp only [SSet.boundary₁.ι₀_desc]
    change SSet.yonedaEquiv.symm
        (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W
          ((pRow W ⦋0⦌).app (op ⦋0⦌) x)) ≫ (rawG W).hom =
      SSet.yonedaEquiv.symm
        ((ell W).hom.app (op ⦋0⦌)
          (JTGtildeOrderedFiberAction.targetVertex W
            ((JTGtildeOrderedFiberAction.gRow W ⦋0⦌).app
              (op ⦋0⦌) x)))
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    simpa only [Equiv.apply_symm_apply] using rawG_zeroGenerator_at_p W x
  · rw [← Category.assoc]
    change (SSet.boundary₁.ι₁ ≫ SSet.boundary₁.desc
        (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W
          (JTProjectiveOrderedFiberComparison.targetVertices W x y).1)
        (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W
          (JTProjectiveOrderedFiberComparison.targetVertices W x y).2)) ≫
          (rawG W).hom =
      SSet.boundary₁.ι₁ ≫ SSet.boundary₁.desc
        ((ell W).hom.app (op ⦋0⦌)
          (JTGtildeOrderedFiberAction.targetVertices W x y).1)
        ((ell W).hom.app (op ⦋0⦌)
          (JTGtildeOrderedFiberAction.targetVertices W x y).2)
    simp only [SSet.boundary₁.ι₁_desc]
    change SSet.yonedaEquiv.symm
        (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W
          ((pRow W ⦋0⦌).app (op ⦋0⦌) y)) ≫ (rawG W).hom =
      SSet.yonedaEquiv.symm
        ((ell W).hom.app (op ⦋0⦌)
          (JTGtildeOrderedFiberAction.targetVertex W
            ((JTGtildeOrderedFiberAction.gRow W ⦋0⦌).app
              (op ⦋0⦌) y)))
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    simpa only [Equiv.apply_symm_apply] using rawG_zeroGenerator_at_p W y

/-- The actual native descent and the raw strict-fiber CE morphism
carry the SAME fixed ordered boundary, in every parameter degree. -/
theorem same_simplex_boundary (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj
      (op ⦋0⦌))
    (k : SimplexCategory)
    (z : (pullback (endpointArrow W)
      (point W (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
        (JTProjectiveOrderedFiberComparison.targetVertices W x y).2)).obj
          (op k)) :
    let a := JTProjectiveOrderedFiberComparison.targetVertices W x y
    let u := (ell W).hom.app (op ⦋0⦌)
      (JTGtildeOrderedFiberAction.targetVertices W x y).1
    let v := (ell W).hom.app (op ⦋0⦌)
      (JTGtildeOrderedFiberAction.targetVertices W x y).2
    let f := ((JTCEOrdinaryFiber.originalFiberCEIso (rawTarget W) u v).hom.app
      (op k)) ((rawStrictFiberMapAtP W x y).app (op k) z)
    let zNative := nativeLabelOfRawFiber W a.1 a.2 k z
    (boundary T).app k ≫ descend W a.1 a.2 T k zNative ≫
      (rawG W).hom = JTXiEndpointCollapse.CE_boundary.app k ≫ f.right := by
  dsimp only
  let a := JTProjectiveOrderedFiberComparison.targetVertices W x y
  let u := (ell W).hom.app (op ⦋0⦌)
    (JTGtildeOrderedFiberAction.targetVertices W x y).1
  let v := (ell W).hom.app (op ⦋0⦌)
    (JTGtildeOrderedFiberAction.targetVertices W x y).2
  let f := ((JTCEOrdinaryFiber.originalFiberCEIso (rawTarget W) u v).hom.app
    (op k)) ((rawStrictFiberMapAtP W x y).app (op k) z)
  have hf : JTXiEndpointCollapse.CE_boundary.app k ≫ f.right =
      JTUnderlyingOrderedFibers.ordinaryBoundary (rawTarget W) u v := by
    have h := f.w
    change JTUnderlyingOrderedFibers.ordinaryBoundary (rawTarget W) u v =
      JTXiEndpointCollapse.CE_boundary.app k ≫ f.right at h
    exact h.symm
  calc
    _ = rawBoundary W a.1 a.2 ≫ (rawG W).hom := by
      rw [← Category.assoc, descend_boundary]
    _ = JTUnderlyingOrderedFibers.ordinaryBoundary (rawTarget W) u v :=
      rawBoundary_image_at_p W x y
    _ = JTXiEndpointCollapse.CE_boundary.app k ≫ f.right := hf.symm

/-- Both coprojections of the ACTUAL native single-edge pushout
identify the descended raw-unit map with the original strict-fiber
CE morphism. This is an equality of the complete maps, not merely
their restrictions to a chosen generator. -/
theorem same_simplex_descended_map (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj
      (op ⦋0⦌))
    (k : SimplexCategory)
    (z : (pullback (endpointArrow W)
      (point W (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
        (JTProjectiveOrderedFiberComparison.targetVertices W x y).2)).obj
          (op k)) :
    let a := JTProjectiveOrderedFiberComparison.targetVertices W x y
    let u := (ell W).hom.app (op ⦋0⦌)
      (JTGtildeOrderedFiberAction.targetVertices W x y).1
    let v := (ell W).hom.app (op ⦋0⦌)
      (JTGtildeOrderedFiberAction.targetVertices W x y).2
    let f := ((JTCEOrdinaryFiber.originalFiberCEIso (rawTarget W) u v).hom.app
      (op k)) ((rawStrictFiberMapAtP W x y).app (op k) z)
    let zNative := nativeLabelOfRawFiber W a.1 a.2 k z
    descend W a.1 a.2 T k zNative ≫ (rawG W).hom =
      singleCylinderToCE k ≫ f.right := by
  dsimp only
  let a := JTProjectiveOrderedFiberComparison.targetVertices W x y
  let u := (ell W).hom.app (op ⦋0⦌)
    (JTGtildeOrderedFiberAction.targetVertices W x y).1
  let v := (ell W).hom.app (op ⦋0⦌)
    (JTGtildeOrderedFiberAction.targetVertices W x y).2
  let f := ((JTCEOrdinaryFiber.originalFiberCEIso (rawTarget W) u v).hom.app
    (op k)) ((rawStrictFiberMapAtP W x y).app (op k) z)
  let zNative := nativeLabelOfRawFiber W a.1 a.2 k z
  have hinterval := same_simplex_rawCE_interval W x y k z
  change ((SSet.yonedaEquiv.symm nativeTop ⊗ₘ
      𝟙 (GroupoidSimplex.parameter.obj k)) ≫
    (cylinder T).app k ≫ descend W a.1 a.2 T k zNative) ≫
    (rawG W).hom = JTXiEndpointCollapse.CE_interval.app k ≫ f.right
      at hinterval
  rw [nativeTop_yoneda] at hinterval
  have hcancel :
      ((singleIso 1).hom ⊗ₘ 𝟙 (GroupoidSimplex.parameter.obj k)) ≫
        ((singleIso 1).inv ⊗ₘ
          𝟙 (GroupoidSimplex.parameter.obj k)) = 𝟙 _ := by
    change ((tensorRight (GroupoidSimplex.parameter.obj k)).map
        (singleIso 1).hom) ≫
      ((tensorRight (GroupoidSimplex.parameter.obj k)).map
        (singleIso 1).inv) = 𝟙 _
    rw [← Functor.map_comp, Iso.hom_inv_id]
    exact (tensorRight (GroupoidSimplex.parameter.obj k)).map_id
      (single 1).toSSet
  have hcylinder :
      (cylinder T).app k ≫
          (descend W a.1 a.2 T k zNative ≫ (rawG W).hom) =
        (cylinder T).app k ≫ (singleCylinderToCE k ≫ f.right) := by
    have hh := congrArg
      (fun q => ((singleIso 1).hom ⊗ₘ
        𝟙 (GroupoidSimplex.parameter.obj k)) ≫ q) hinterval
    have hh' :
        (cylinder T).app k ≫
            (descend W a.1 a.2 T k zNative ≫ (rawG W).hom) =
          ((singleIso 1).hom ⊗ₘ
            𝟙 (GroupoidSimplex.parameter.obj k)) ≫
            (JTXiEndpointCollapse.CE_interval.app k ≫ f.right) := by
      calc
        _ = (((singleIso 1).hom ⊗ₘ
              𝟙 (GroupoidSimplex.parameter.obj k)) ≫
              ((singleIso 1).inv ⊗ₘ
                𝟙 (GroupoidSimplex.parameter.obj k))) ≫
              (cylinder T).app k ≫
                (descend W a.1 a.2 T k zNative ≫ (rawG W).hom) := by
          rw [hcancel, Category.id_comp]
        _ = ((singleIso 1).hom ⊗ₘ
              𝟙 (GroupoidSimplex.parameter.obj k)) ≫
              (((singleIso 1).inv ⊗ₘ
                𝟙 (GroupoidSimplex.parameter.obj k)) ≫
                (cylinder T).app k ≫ descend W a.1 a.2 T k zNative ≫
                  (rawG W).hom) := by simp only [Category.assoc]
        _ = _ := hh
    calc
      _ = ((singleIso 1).hom ⊗ₘ
            𝟙 (GroupoidSimplex.parameter.obj k)) ≫
              (JTXiEndpointCollapse.CE_interval.app k ≫ f.right) := hh'
      _ = (cylinder T).app k ≫ (singleCylinderToCE k ≫ f.right) := by
        calc
          _ = (((singleIso 1).hom ⊗ₘ
                𝟙 (GroupoidSimplex.parameter.obj k)) ≫
                JTXiEndpointCollapse.CE_interval.app k) ≫ f.right :=
            (Category.assoc _ _ _).symm
          _ = ((cylinder T).app k ≫ singleCylinderToCE k) ≫
                f.right := by rw [singleCylinderToCE_cylinder]
          _ = _ := Category.assoc _ _ _
  have hboundary := same_simplex_boundary W x y k z
  change (boundary T).app k ≫ descend W a.1 a.2 T k zNative ≫
      (rawG W).hom = JTXiEndpointCollapse.CE_boundary.app k ≫ f.right
        at hboundary
  apply (isPushout T k).hom_ext
  · exact hcylinder
  · change (boundary T).app k ≫
        (descend W a.1 a.2 T k zNative ≫ (rawG W).hom) =
      (boundary T).app k ≫ (singleCylinderToCE k ≫ f.right)
    calc
      _ = JTXiEndpointCollapse.CE_boundary.app k ≫ f.right := hboundary
      _ = ((boundary T).app k ≫ singleCylinderToCE k) ≫ f.right := by
        rw [singleCylinderToCE_boundary]
      _ = _ := Category.assoc _ _ _

end

end DaggerModels.PartII.JTRawSingleOrderedLabelIso
