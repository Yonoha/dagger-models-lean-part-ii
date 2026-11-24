import DaggerModelsPartII.JTRawFiberEvaluatorComparison
import DaggerModelsPartII.JTOrderedFrameHomBar
import DaggerModelsPartII.JTSingleCylinderCEIso
import DaggerModelsPartII.JTRawSingleOrderedLabelIso

/-! Exact evaluator transport along the original one-edge
cylinder/CE comparison, retaining the degree and ordered endpoints. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTRawCEEvaluatorTransport

open JTOrderedFrameHomBar

noncomputable section

private abbrev Boundary := JTXiEndpointCollapse.boundary
private abbrev Single :=
  JTNecklaceEndpointCylinder.under
    (DaggerChosenRigidificationNecklace.NecklaceCode.single 1)
private abbrev CE :=
  Under.lift JTXiEndpointCollapse.CE JTXiEndpointCollapse.CE_boundary
private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

private theorem castMap_post_eqToHom {C D : SimplicialCat.{0, 0}}
    (f : C ⟶ D) (a b : C.Obj) {x y x' y' : D.Obj}
    (hx : f.obj a = x) (hy : f.obj b = y)
    (ex : x = x') (ey : y = y')
    (h : D.enriched.Hom x y = D.enriched.Hom x' y') :
    OriginalOrdinaryMovingHomColimits.castMap f a b x y hx hy ≫ eqToHom h =
      OriginalOrdinaryMovingHomColimits.castMap f a b x' y'
        (hx.trans ex) (hy.trans ey) := by
  cases ex
  cases ey
  cases h
  simp

/-- The actual, boundary-preserving cosimplicial frame map. -/
def singleToCE : Single ⟶ CE :=
  JTSingleCylinderCEIso.comparison.hom

/-- The one-edge cylinder bar and the CE bar evaluate compatibly on
every full Hom simplex and every cosimplicial degree. -/
theorem single_ce_evaluator_square (U : Under Boundary) :
    toRestrictedBar U (singleToCE) ≫ evaluator Single U =
      toFrameBar U (singleToCE) ≫ evaluator CE U :=
  evaluator_square U (singleToCE)

/-- Its index restriction has the original full-map action; no
endpoint or coefficient is forgotten. -/
theorem single_ce_restrict_degree (U : Under Boundary) :
    restrict U (singleToCE) ⋙ degree Single U = degree CE U :=
  restrict_degree U (singleToCE)

/-- The same full frame comparison transfers evaluator weakness when
the two original ordered Hom weights satisfy the stated contractibility
conditions. -/
theorem single_ce_evaluator_weak_iff (U : Under Boundary)
    (hSingle : ∀ k, DaggerSSetGluing.GW
      (DaggerOriginalProductGadget.pointMap
        ((Single ⋙ orderedHom).obj k)))
    (hCE : ∀ k, DaggerSSetGluing.GW
      (DaggerOriginalProductGadget.pointMap
        ((CE ⋙ orderedHom).obj k))) :
    WeakEquivalence (evaluator Single U) ↔
      WeakEquivalence (evaluator CE U) := by
  haveI : IsIso (singleToCE) := by
    change IsIso JTSingleCylinderCEIso.comparison.hom
    infer_instance
  haveI : IsIso (EndpointMappingFiber.precomp (Z := U) singleToCE) := by
    change IsIso
      (Functor.isoWhiskerRight
        (NatIso.op JTSingleCylinderCEIso.comparison) (yoneda.obj U)).hom
    infer_instance
  have hrestrict : WeakEquivalence
      (EndpointMappingFiber.precomp (Z := U) singleToCE) := inferInstance
  exact evaluator_weak_iff U singleToCE hrestrict hSingle hCE

private abbrev rawFiber (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :=
  pullback (JTProjectiveOrderedFiberComparison.endpointArrow W)
    (JTProjectiveOrderedFiberComparison.point W
      (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
      (JTProjectiveOrderedFiberComparison.targetVertices W x y).2)

private abbrev decorated (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :=
  JTRawFiberToDecoratedIndex.toDecorated W
    (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
    (JTProjectiveOrderedFiberComparison.targetVertices W x y).2

private abbrev homWeights (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :=
  DecoratedNecklaceHomDiagram.cylinderHomDiagram W
    (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
    (JTProjectiveOrderedFiberComparison.targetVertices W x y).2

/-- Reindexing the entire strict-fiber coefficient on a constant chain
gives exactly the constant decorated coefficient at its image label. -/
theorem toEvaluatorBar_section (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌))
    (i : (rawFiber W x y).Elementsᵒᵖ) :
    ReplacementConstantSections.sectionMap
        (decorated W x y ⋙ homWeights W x y) i ≫
      JTRawFiberEvaluatorComparison.toEvaluatorBar W x y =
    ReplacementConstantSections.sectionMap (homWeights W x y)
      ((decorated W x y).obj i) := by
  apply NatTrans.ext
  rfl

/-- The actual raw strict-fiber bar evaluator, on every full constant-chain
coefficient, is the original decorated post-raw cocone component. -/
theorem rawBar_section_evaluator (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌))
    (i : (rawFiber W x y).Elementsᵒᵖ) :
    ReplacementConstantSections.sectionMap
        (decorated W x y ⋙ homWeights W x y) i ≫
      DaggerNativeSimplicialReplacement.diagonalAugmentation
        (decorated W x y ⋙ homWeights W x y)
        (Functor.whiskerLeft (decorated W x y)
          (DecoratedRawUnitHomCalibration.postRawRightMapAtP W x y)) =
    (DecoratedRawUnitHomCalibration.postRawRightMapAtP W x y).app
      ((decorated W x y).obj i) := by
  rw [← JTRawFiberEvaluatorComparison.evaluator_triangle W x y]
  rw [← Category.assoc, toEvaluatorBar_section]
  exact DecoratedRawUnitHomCalibration.wholeBarPostRaw_section W x y
    ((decorated W x y).obj i)

/-- At each original raw strict-fiber simplex, the full Hom coefficient
evaluates by the original native one-edge descended label. -/
theorem rawBar_single_section_evaluator (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌))
    (k : SimplexCategory) (z : (rawFiber W x y).obj (op k)) :
    let i := op ((rawFiber W x y).elementsMk (op k) z)
    ReplacementConstantSections.sectionMap
        (decorated W x y ⋙ homWeights W x y) i ≫
      DaggerNativeSimplicialReplacement.diagonalAugmentation
        (decorated W x y ⋙ homWeights W x y)
        (Functor.whiskerLeft (decorated W x y)
          (DecoratedRawUnitHomCalibration.postRawRightMapAtP W x y)) =
    DecoratedRawUnitHomCalibration.compositeHomAtP W x y
      (DaggerChosenRigidificationNecklace.NecklaceCode.single 1) k
      (JTRawSingleOrderedLabelIso.nativeLabelOfRawFiber W
        (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
        (JTProjectiveOrderedFiberComparison.targetVertices W x y).2 k z) := by
  dsimp only
  rw [rawBar_section_evaluator]
  change (DecoratedRawUnitHomCalibration.postRawRightMapAtP W x y).app
    (OrderedLabelElements.mk W
      (OrderedNecklaceVertexPoints.boundaryPoint W
        (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
        (JTProjectiveOrderedFiberComparison.targetVertices W x y).2)
      (DaggerChosenRigidificationNecklace.NecklaceCode.single 1) k
      (JTRawSingleOrderedLabelIso.nativeLabelOfRawFiber W
        (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
        (JTProjectiveOrderedFiberComparison.targetVertices W x y).2 k z)) = _
  exact DecoratedRawUnitHomCalibration.postRawRightMapAtP_app W x y _

private abbrev u (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :=
  (JTRawFreeInnerComparison.ell W).hom.app (op ⦋0⦌)
    (JTGtildeOrderedFiberAction.targetVertices W x y).1

private abbrev v (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :=
  (JTRawFreeInnerComparison.ell W).hom.app (op ⦋0⦌)
    (JTGtildeOrderedFiberAction.targetVertices W x y).2

/-- The same raw target with its literal ordered boundary. -/
def ceTarget (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    Under Boundary :=
  Under.mk (JTUnderlyingOrderedFibers.ordinaryBoundary
    (JTRawFreeInnerComparison.rawTarget W) (u W x y) (v W x y))

/-- The actual raw strict-fiber map, carried into the original CE
under-boundary Hom presentation. -/
def rawToCE (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    rawFiber W x y ⟶ EndpointMappingFiber.mapping (Z := ceTarget W x y) CE :=
  JTRawUnitCylinderCalibration.rawStrictFiberMapAtP W x y ≫
    (JTCEOrdinaryFiber.originalFiberCEIso
      (JTRawFreeInnerComparison.rawTarget W) (u W x y) (v W x y)).hom

/-- The entire category-of-elements map of the actual raw strict-fiber
action, retaining every original simplicial degree. -/
def rawToCEIndex (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    (rawFiber W x y).Elementsᵒᵖ ⥤
      JTOrderedFrameHomBar.Index CE (ceTarget W x y) :=
  (NatTrans.mapElements (rawToCE W x y)).op

/-- At each degree, the literal single cylinder Hom is the ordered Hom
of the original under-boundary frame. -/
theorem singleCylinderHom_eq_orderedHom (k : SimplexCategory) :
    NecklaceCylinderHomSpan.cylinderHom
      (DaggerChosenRigidificationNecklace.NecklaceCode.single 1) k =
        orderedHom.obj (Single.obj k) := rfl

/-- Pulling the decorated cylinder weights back to the raw strict fiber
gives the degree-whiskered original one-edge frame weights, on both
objects and every operator. -/
theorem rawSingleWeights_eq (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    decorated W x y ⋙ homWeights W x y =
      (CategoryOfElements.π (rawFiber W x y)).op ⋙
        unopUnop SimplexCategory ⋙ Single ⋙ orderedHom := by
  refine CategoryTheory.Functor.ext (fun i ↦ ?_) ?_
  · rfl
  · intro i j f
    have hfirst :
        ((OrderedLabelElements.projection W
          (OrderedNecklaceVertexPoints.boundaryPoint W
            (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
            (JTProjectiveOrderedFiberComparison.targetVertices W x y).2)).map
            ((decorated W x y).map f)).1 =
          𝟙 (DaggerChosenRigidificationNecklace.NecklaceCode.single 1) := by
      rfl
    have hproj :
        (OrderedLabelElements.projection W
          (OrderedNecklaceVertexPoints.boundaryPoint W
            (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
            (JTProjectiveOrderedFiberComparison.targetVertices W x y).2)).map
            ((decorated W x y).map f) =
          (𝟙 (DaggerChosenRigidificationNecklace.NecklaceCode.single 1),
            (unopUnop SimplexCategory).map
              ((CategoryOfElements.π (rawFiber W x y)).op.map f)) := by
      apply Prod.ext
      · exact hfirst
      · rfl
    dsimp only [Functor.comp_map]
    apply OriginalOrdinaryMovingHomColimits.castMap_congr
    change OrdinaryRigidification.rigidification.map
      ((DecoratedNecklaceHomDiagram.cylinderDiagram W
        (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
        (JTProjectiveOrderedFiberComparison.targetVertices W x y).2).map
          ((decorated W x y).map f)) =
      OrdinaryRigidification.rigidification.map
        ((JTNecklaceEndpointCylinder.value
          (DaggerChosenRigidificationNecklace.NecklaceCode.single 1)).map
            ((unopUnop SimplexCategory).map
              ((CategoryOfElements.π (rawFiber W x y)).op.map f)))
    congr 1
    dsimp only [DecoratedNecklaceHomDiagram.cylinderDiagram, Functor.comp_map]
    rw [hproj]
    change JTNecklaceEndpointCylinder.nativeMap
      (𝟙 (DaggerChosenRigidificationNecklace.NecklaceCode.single 1)) _ ≫
        (JTNecklaceEndpointCylinder.value
          (DaggerChosenRigidificationNecklace.NecklaceCode.single 1)).map _ = _
    rw [JTNecklaceEndpointCylinder.nativeMap_id, Category.id_comp]

/-- The raw map changes the label and its value, not its parameter
degree. -/
theorem rawToCEIndex_degree (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    rawToCEIndex W x y ⋙ JTOrderedFrameHomBar.degree CE (ceTarget W x y) =
      (CategoryOfElements.π (rawFiber W x y)).op ⋙
        unopUnop SimplexCategory := rfl

/-- The pulled-back decorated evaluator after the original rawG
postcomposition, written against the same CE target Hom. -/
private def rawTargetHom (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    SSet.{0} :=
  (DaggerModels.OrdinaryRigidification.RigidificationVertices.vertexEquiv
      (JTRawFreeInnerComparison.rawTarget W).toSSet (u W x y) ⟶[SSet.{0}]
    DaggerModels.OrdinaryRigidification.RigidificationVertices.vertexEquiv
      (JTRawFreeInnerComparison.rawTarget W).toSSet (v W x y))

def rawBarEvaluator (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    JTRawFiberEvaluatorComparison.strictFiberBar W x y ⟶
      rawTargetHom W x y :=
  DaggerNativeSimplicialReplacement.diagonalAugmentation
    (decorated W x y ⋙ homWeights W x y)
    (Functor.whiskerLeft (decorated W x y)
      (DecoratedRawUnitHomCalibration.postRawRightMapAtP W x y))

private theorem ceTarget_first (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    BoundaryNecklaceComma.first (ceTarget W x y) = u W x y :=
  congrArg Prod.fst
    ((JTEndpointObjects.boundaryHomEquiv
      (JTRawFreeInnerComparison.rawTarget W).toSSet).apply_symm_apply
        (u W x y, v W x y))

private theorem ceTarget_last (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    BoundaryNecklaceComma.last (ceTarget W x y) = v W x y :=
  congrArg Prod.snd
    ((JTEndpointObjects.boundaryHomEquiv
      (JTRawFreeInnerComparison.rawTarget W).toSSet).apply_symm_apply
        (u W x y, v W x y))

/-- Ordered-Hom target identification induced by the original two
boundary vertices, without changing the raw coefficient. -/
def rawTargetHomIso (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    rawTargetHom W x y ≅ orderedHom.obj (ceTarget W x y) :=
  eqToIso (by
    change (DaggerModels.OrdinaryRigidification.rigidification.obj
      (JTRawFreeInnerComparison.rawTarget W).toSSet).enriched.Hom
        (DaggerModels.OrdinaryRigidification.RigidificationVertices.vertexEquiv
          (JTRawFreeInnerComparison.rawTarget W).toSSet (u W x y))
        (DaggerModels.OrdinaryRigidification.RigidificationVertices.vertexEquiv
          (JTRawFreeInnerComparison.rawTarget W).toSSet (v W x y)) =
      (DaggerModels.OrdinaryRigidification.rigidification.obj
      (JTRawFreeInnerComparison.rawTarget W).toSSet).enriched.Hom
        (DaggerModels.OrdinaryRigidification.RigidificationVertices.vertexEquiv
          (JTRawFreeInnerComparison.rawTarget W).toSSet
            (BoundaryNecklaceComma.first (ceTarget W x y)))
        (DaggerModels.OrdinaryRigidification.RigidificationVertices.vertexEquiv
          (JTRawFreeInnerComparison.rawTarget W).toSSet
            (BoundaryNecklaceComma.last (ceTarget W x y)))
    rw [ceTarget_first, ceTarget_last])

/-- Forget only the full ordered Hom coefficient from the raw strict-fiber
bar; the entire original simplex label remains. -/
def rawBarProjection (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    JTRawFiberEvaluatorComparison.strictFiberBar W x y ⟶
      nerve ((rawFiber W x y).Elementsᵒᵖ) :=
  DaggerNativeSimplicialReplacement.diagonalProjection
    (decorated W x y ⋙ homWeights W x y)

theorem rawBarProjection_weak (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    WeakEquivalence (rawBarProjection W x y) :=
  (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
    (DaggerNativeSimplicialReplacement.diagonalProjection_GW
      (decorated W x y ⋙ homWeights W x y)
      (fun i => DecoratedCylinderNecklacePresentation.cylinderHom_point_GW W
        (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
        (JTProjectiveOrderedFiberComparison.targetVertices W x y).2
        ((decorated W x y).obj i)))

/-- The corresponding CE bar projection retains every map from the
actual CE frame and its full parameter degree. -/
def ceBarProjection (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    bar CE (ceTarget W x y) ⟶
      nerve (JTOrderedFrameHomBar.Index CE (ceTarget W x y)) :=
  DaggerNativeSimplicialReplacement.diagonalProjection
    (weights CE (ceTarget W x y))

/-- The original one-edge cylinder-to-CE frame map, applied to every
complete ordered Hom coefficient of the raw strict-fiber index. -/
def rawWeightChange (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    decorated W x y ⋙ homWeights W x y ⟶
      rawToCEIndex W x y ⋙ weights CE (ceTarget W x y) :=
  (eqToHom (rawSingleWeights_eq W x y) :
    decorated W x y ⋙ homWeights W x y ⟶
      (CategoryOfElements.π (rawFiber W x y)).op ⋙
        unopUnop SimplexCategory ⋙ Single ⋙ orderedHom) ≫
    Functor.whiskerLeft
      ((CategoryOfElements.π (rawFiber W x y)).op ⋙ unopUnop SimplexCategory)
      (Functor.whiskerRight singleToCE orderedHom)

theorem rawWeightChange_app (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌))
    (i : (rawFiber W x y).Elementsᵒᵖ) :
    (rawWeightChange W x y).app i =
      orderedHom.map
        (singleToCE.app
          (((CategoryOfElements.π (rawFiber W x y)).op ⋙
            unopUnop SimplexCategory).obj i)) := by
  simp only [rawWeightChange, NatTrans.comp_app, eqToHom_app]
  rw [show Functor.congr_obj (rawSingleWeights_eq W x y) i = rfl from
    Subsingleton.elim _ _]
  rfl

/-- Change every full coefficient by the original cylinder-to-CE map,
then reindex every chain by the actual raw-to-CE map. -/
def rawCEBarMap (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    JTRawFiberEvaluatorComparison.strictFiberBar W x y ⟶
      bar CE (ceTarget W x y) :=
  DaggerNativeSimplicialReplacementWeightsChange.diagonalChange
    (rawWeightChange W x y) ≫
      DaggerNativeSimplicialReplacementReindex.diagonalReindex
        (rawToCEIndex W x y) (weights CE (ceTarget W x y))

theorem rawCEBarMap_projection_square (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    rawCEBarMap W x y ≫ ceBarProjection W x y =
      rawBarProjection W x y ≫ nerveMap (rawToCEIndex W x y) := by
  unfold rawCEBarMap ceBarProjection rawBarProjection
  rw [Category.assoc,
    DaggerNativeSimplicialReplacementReindex.projection_square,
    ← Category.assoc,
    DaggerNativeSimplicialReplacementWeightsChange.projection_square]

private theorem component_square (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌))
    (k : SimplexCategory) (z : (rawFiber W x y).obj (op k)) :
    DecoratedRawUnitHomCalibration.compositeHomAtP W x y
        (DaggerChosenRigidificationNecklace.NecklaceCode.single 1) k
        (JTRawSingleOrderedLabelIso.nativeLabelOfRawFiber W
          (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
          (JTProjectiveOrderedFiberComparison.targetVertices W x y).2 k z) ≫
      (rawTargetHomIso W x y).hom =
    orderedHom.map (singleToCE.app k) ≫
      orderedHom.map
        (((JTCEOrdinaryFiber.originalFiberCEIso
          (JTRawFreeInnerComparison.rawTarget W) (u W x y) (v W x y)).hom.app
            (op k)) ((JTRawUnitCylinderCalibration.rawStrictFiberMapAtP W x y).app
              (op k) z)) := by
  rw [← orderedHom.map_comp]
  have hs := DecoratedRawUnitHomCalibration.single_postRaw_eq_CE W x y k z
  dsimp only at hs
  rw [hs]
  simp only [JTOrderedFrameHomBar.orderedHom_map, rawTargetHomIso]
  apply castMap_post_eqToHom
  · change DaggerChosenRigidificationNecklace.RV
        (JTRawFreeInnerComparison.rawTarget W).toSSet (u W x y) =
      DaggerChosenRigidificationNecklace.RV
        (JTRawFreeInnerComparison.rawTarget W).toSSet
          (BoundaryNecklaceComma.first (ceTarget W x y))
    rw [ceTarget_first]
  · change DaggerChosenRigidificationNecklace.RV
        (JTRawFreeInnerComparison.rawTarget W).toSSet (v W x y) =
      DaggerChosenRigidificationNecklace.RV
        (JTRawFreeInnerComparison.rawTarget W).toSSet
          (BoundaryNecklaceComma.last (ceTarget W x y))
    rw [ceTarget_last]
  · change rawTargetHom W x y = orderedHom.obj (ceTarget W x y)
    change (DaggerModels.OrdinaryRigidification.rigidification.obj
        (JTRawFreeInnerComparison.rawTarget W).toSSet).enriched.Hom
          (DaggerModels.OrdinaryRigidification.RigidificationVertices.vertexEquiv
            (JTRawFreeInnerComparison.rawTarget W).toSSet (u W x y))
          (DaggerModels.OrdinaryRigidification.RigidificationVertices.vertexEquiv
            (JTRawFreeInnerComparison.rawTarget W).toSSet (v W x y)) =
      (DaggerModels.OrdinaryRigidification.rigidification.obj
        (JTRawFreeInnerComparison.rawTarget W).toSSet).enriched.Hom
          (DaggerModels.OrdinaryRigidification.RigidificationVertices.vertexEquiv
            (JTRawFreeInnerComparison.rawTarget W).toSSet
              (BoundaryNecklaceComma.first (ceTarget W x y)))
          (DaggerModels.OrdinaryRigidification.RigidificationVertices.vertexEquiv
            (JTRawFreeInnerComparison.rawTarget W).toSSet
              (BoundaryNecklaceComma.last (ceTarget W x y)))
    rw [ceTarget_first, ceTarget_last]

theorem rawCECocone_square (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    Functor.whiskerLeft (decorated W x y)
        (DecoratedRawUnitHomCalibration.postRawRightMapAtP W x y) ≫
      (Functor.const ((rawFiber W x y).Elementsᵒᵖ)).map
        (rawTargetHomIso W x y).hom =
      rawWeightChange W x y ≫
        Functor.whiskerLeft (rawToCEIndex W x y)
          (cocone CE (ceTarget W x y)) := by
  apply NatTrans.ext
  funext i
  induction i using Opposite.rec with
  | op i =>
    rcases i with ⟨k, z⟩
    induction k using Opposite.rec with
    | op k =>
      change (DecoratedRawUnitHomCalibration.postRawRightMapAtP W x y).app
          ((decorated W x y).obj
            (op ((rawFiber W x y).elementsMk (op k) z))) ≫
            (rawTargetHomIso W x y).hom =
        (rawWeightChange W x y).app
          (op ((rawFiber W x y).elementsMk (op k) z)) ≫
          orderedHom.map
            ((rawToCEIndex W x y).obj
              (op ((rawFiber W x y).elementsMk (op k) z))).unop.2
      rw [rawWeightChange_app]
      change (DecoratedRawUnitHomCalibration.postRawRightMapAtP W x y).app
          (OrderedLabelElements.mk W
            (OrderedNecklaceVertexPoints.boundaryPoint W
              (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
              (JTProjectiveOrderedFiberComparison.targetVertices W x y).2)
            (DaggerChosenRigidificationNecklace.NecklaceCode.single 1) k
            (JTRawSingleOrderedLabelIso.nativeLabelOfRawFiber W
              (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
              (JTProjectiveOrderedFiberComparison.targetVertices W x y).2 k z)) ≫
            (rawTargetHomIso W x y).hom = _
      rw [DecoratedRawUnitHomCalibration.postRawRightMapAtP_app]
      change DecoratedRawUnitHomCalibration.compositeHomAtP W x y
          (DaggerChosenRigidificationNecklace.NecklaceCode.single 1) k
          (JTRawSingleOrderedLabelIso.nativeLabelOfRawFiber W
            (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
            (JTProjectiveOrderedFiberComparison.targetVertices W x y).2 k z) ≫
            (rawTargetHomIso W x y).hom = _
      exact component_square W x y k z

/-- The exact natural component equality suffices for the evaluation
square of the actual full-bar comparison. -/
theorem rawCEBarMap_evaluator_square_of_cocone (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌))
    (hCocone :
      Functor.whiskerLeft (decorated W x y)
          (DecoratedRawUnitHomCalibration.postRawRightMapAtP W x y) ≫
        (Functor.const ((rawFiber W x y).Elementsᵒᵖ)).map
          (rawTargetHomIso W x y).hom =
        rawWeightChange W x y ≫
          Functor.whiskerLeft (rawToCEIndex W x y)
            (cocone CE (ceTarget W x y))) :
    rawBarEvaluator W x y ≫ (rawTargetHomIso W x y).hom =
      rawCEBarMap W x y ≫ evaluator CE (ceTarget W x y) := by
  unfold rawCEBarMap JTOrderedFrameHomBar.evaluator
  rw [Category.assoc,
    DaggerNativeSimplicialReplacementReindex.augmentation_square,
    DaggerNativeSimplicialReplacementWeightsChange.augmentation_square]
  apply NatTrans.ext
  funext q c
  exact congrFun (NatTrans.congr_app
    (NatTrans.congr_app hCocone
      (DaggerNativeSimplicialReplacementCells.first c.1)) q) c.2

theorem ceBarProjection_weak (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌))
    (hCEWeight : ∀ k, DaggerSSetGluing.GW
      (DaggerOriginalProductGadget.pointMap ((CE ⋙ orderedHom).obj k))) :
    WeakEquivalence (ceBarProjection W x y) :=
  (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
    (DaggerNativeSimplicialReplacement.diagonalProjection_GW
      (weights CE (ceTarget W x y))
      (fun i ↦ hCEWeight ((degree CE (ceTarget W x y)).obj i)))

/-- The two exact natural squares needed to extend the checked
single-simplex CE equality to all chains and full Hom coefficients. -/
structure RawCEBarComparison (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) where
  barMap : JTRawFiberEvaluatorComparison.strictFiberBar W x y ⟶
    bar CE (ceTarget W x y)
  projection_square :
    barMap ≫ ceBarProjection W x y =
      rawBarProjection W x y ≫ nerveMap (rawToCEIndex W x y)
  evaluator_square :
    rawBarEvaluator W x y ≫ (rawTargetHomIso W x y).hom =
      barMap ≫ evaluator CE (ceTarget W x y)

/-- Once the literal coefficient cocones agree, the checked full-bar
map supplies both required natural squares. -/
def rawCEBarComparison_of_cocone (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌))
    (hCocone :
      Functor.whiskerLeft (decorated W x y)
          (DecoratedRawUnitHomCalibration.postRawRightMapAtP W x y) ≫
        (Functor.const ((rawFiber W x y).Elementsᵒᵖ)).map
          (rawTargetHomIso W x y).hom =
        rawWeightChange W x y ≫
          Functor.whiskerLeft (rawToCEIndex W x y)
            (cocone CE (ceTarget W x y))) :
    RawCEBarComparison W x y where
  barMap := rawCEBarMap W x y
  projection_square := rawCEBarMap_projection_square W x y
  evaluator_square := rawCEBarMap_evaluator_square_of_cocone W x y hCocone

/-- The actual full-bar comparison satisfies both natural squares,
with no extra comparison hypothesis. -/
def rawCEBarComparison (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    RawCEBarComparison W x y :=
  rawCEBarComparison_of_cocone W x y (rawCECocone_square W x y)

/-- Given an exact full-bar comparison, the two evaluator weak equivalences
transfer weakness to the literal original raw strict-fiber map. -/
theorem rawToCE_weak_of_bar_comparison (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌))
    (hW : @IsFibrant Source _ SegalLocalizers.injectiveSegalModel.categoryWithFibrations _ W)
    (hDecorated : WeakEquivalence
      (DecoratedNecklaceHomBar.evaluator W
        (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
        (JTProjectiveOrderedFiberComparison.targetVertices W x y).2))
    (hCE : WeakEquivalence (evaluator CE (ceTarget W x y)))
    (hCEWeight : ∀ k, DaggerSSetGluing.GW
      (DaggerOriginalProductGadget.pointMap ((CE ⋙ orderedHom).obj k)))
    (B : RawCEBarComparison W x y) :
    WeakEquivalence (rawToCE W x y) := by
  letI : WeakEquivalence (evaluator CE (ceTarget W x y)) := hCE
  haveI : WeakEquivalence (rawBarEvaluator W x y) :=
    (JTRawFiberEvaluatorComparison.restricted_evaluator_weak_iff W x y hW).mpr hDecorated
  haveI : WeakEquivalence B.barMap := by
    have hcomp : WeakEquivalence
        (B.barMap ≫ evaluator CE (ceTarget W x y)) := by
      rw [← B.evaluator_square]
      infer_instance
    exact (weakEquivalence_postcomp_iff B.barMap
      (evaluator CE (ceTarget W x y))).mp hcomp
  letI : WeakEquivalence (ceBarProjection W x y) :=
    ceBarProjection_weak W x y hCEWeight
  letI : WeakEquivalence (rawBarProjection W x y) :=
    rawBarProjection_weak W x y
  haveI : WeakEquivalence (nerveMap (rawToCEIndex W x y)) := by
    have hcomp : WeakEquivalence
        (rawBarProjection W x y ≫ nerveMap (rawToCEIndex W x y)) := by
      rw [← B.projection_square]
      infer_instance
    exact (weakEquivalence_precomp_iff (rawBarProjection W x y)
      (nerveMap (rawToCEIndex W x y))).mp hcomp
  have hindex : WeakEquivalence
      (nerveMap (NatTrans.mapElements (rawToCE W x y)).op) := by
    change WeakEquivalence (nerveMap (rawToCEIndex W x y))
    infer_instance
  exact (TotalElementsWeakComparison.elementsOpposite_weak_iff
    (rawToCE W x y)).mp hindex

/-- The literal original raw strict-fiber map is weak when the two
evaluators are weak and the CE weights are contractible. The actual
full-bar comparison supplies both natural squares. -/
theorem rawStrictFiberMapAtP_weak_of_evaluators (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌))
    (hW : @IsFibrant Source _ SegalLocalizers.injectiveSegalModel.categoryWithFibrations _ W)
    (hDecorated : WeakEquivalence
      (DecoratedNecklaceHomBar.evaluator W
        (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
        (JTProjectiveOrderedFiberComparison.targetVertices W x y).2))
    (hCE : WeakEquivalence (evaluator CE (ceTarget W x y)))
    (hCEWeight : ∀ k, DaggerSSetGluing.GW
      (DaggerOriginalProductGadget.pointMap ((CE ⋙ orderedHom).obj k))) :
    WeakEquivalence (JTRawUnitCylinderCalibration.rawStrictFiberMapAtP W x y) := by
  have h : WeakEquivalence (rawToCE W x y) :=
    rawToCE_weak_of_bar_comparison W x y hW hDecorated hCE hCEWeight
      (rawCEBarComparison W x y)
  exact (weakEquivalence_postcomp_iff _ _).mp h


end

end DaggerModels.PartII.JTRawCEEvaluatorTransport
