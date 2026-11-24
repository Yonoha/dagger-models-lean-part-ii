import DaggerModelsPartII.JTXiChosenFiber
import DaggerModelsPartII.JTXiEndpointMappingFibration
import DaggerModelsPartII.JTDerivedOrderedMate
import DaggerModelsPartII.JTEndpointReplacementSquare
import DaggerModelsPartII.ChosenHomotopyFiberTriangle

/-!
# The actual qX comparison of the chosen Xi endpoint fiber

The comparison is defined by the two components of the literal zero-fixed
qX arrow replacement. Its source is the chosen homotopy fiber of the original
composite-nerve endpoint arrow, and its target is the strict under-boundary
Hom of the actual QX endpoint frame. The calibration with the retained raw
Xi comparison is established on the two pullback projections.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTXiChosenFiberComparison

open JTRelativeReedyFrame JTEndpointArrowReplacement JTEndpointAugmentations
open JTEndpointCobaseAugmentations JTEndpointFrames JTEndpointHom
open JTActualCosimplicialFrame JTOrderedFrameMate JTXiRowEndpoints
open ArrowReedyCornerInterchange JTXiAugmentation

noncomputable section

private local instance : HasLimits Coefficient := daggerSimplicialCatHasLimits
private local instance : HasColimits Coefficient := daggerSimplicialCatHasColimits
private local instance : ModelCategory Coefficient :=
  DaggerActualRigidificationQuillen.modelG.{0}

/-- The source component of the actual qX arrow replacement, with the
opposite variance required by the native strict-mapping functor. -/
def qXiSource : X.op ⋙ (Arrow.leftFunc (C := Coefficient)).op ⟶
    JTXiEndpointMappingFibration.qXiSourceOp :=
  Functor.whiskerRight (NatTrans.op qX) (Arrow.leftFunc (C := Coefficient)).op

/-- The target component of the same literal qX replacement. -/
def qXiTarget : X.op ⋙ (Arrow.rightFunc (C := Coefficient)).op ⟶
    JTXiEndpointMappingFibration.qXiTargetOp :=
  Functor.whiskerRight (NatTrans.op qX) (Arrow.rightFunc (C := Coefficient)).op

/-- The endpoint arrow of the actual qX source-to-target diagram. -/
def resolvedArrow (C : Coefficient) :=
  EndpointMappingFiber.precomp (Z := C) (structureMap QX)

/-- The actual total map, beginning with the checked original composite-nerve
row identification and ending with precomposition by qX's target component. -/
def totalComparison (C : Coefficient) :
    xiRow C oneIndex ⟶ EndpointMappingFiber.mapping (Z := C) (target QX) :=
  (xiRowMappingIso C oneIndex).hom ≫
    (StrictFrameMappingWeak.strictMapping C).map qXiTarget

/-- The base map retains the categorical original pair, its ordered
pointwise pair presentation, and then the literal qX source component. -/
def baseComparison (C : Coefficient) :
    xiCategoricalZeroPairRow C ⟶
      EndpointMappingFiber.mapping (Z := C) (source QX) :=
  (xiCategoricalPairIso C).hom ≫ (xiZeroPairIso C).hom ≫
    (StrictFrameMappingWeak.strictMapping C).map qXiSource

/-- The qX arrow components commute with the literal endpoint-face arrow. -/
private theorem qXi_mapping_square (C : Coefficient) :
    EndpointMappingFiber.precomp (Z := C) (endpointFaces XiCurried) ≫
        (StrictFrameMappingWeak.strictMapping C).map qXiSource =
      (StrictFrameMappingWeak.strictMapping C).map qXiTarget ≫
        resolvedArrow C := by
  have h : structureOpp X.op ≫ qXiSource =
      qXiTarget ≫ structureOpp QXop := by
    apply NatTrans.ext
    funext k
    change ((qX.app k.unop).left ≫ (X.obj k.unop).hom).op =
      ((QX.obj k.unop).hom ≫ (qX.app k.unop).right).op
    exact congrArg Quiver.Hom.op (Arrow.w (qX.app k.unop))
  simpa only [resolvedArrow, Functor.map_comp] using
    congrArg ((StrictFrameMappingWeak.strictMapping C).map) h

/-- The original categorical endpoint arrow and the resolved qX endpoint
arrow form the square specified by the actual qX component maps. -/
theorem mapping_square (C : Coefficient) :
    xiEndpointArrow C ≫ baseComparison C =
      totalComparison C ≫ resolvedArrow C := by
  calc
    xiEndpointArrow C ≫ baseComparison C =
        ((xiRowMappingIso C oneIndex).hom ≫
          EndpointMappingFiber.precomp (Z := C) (endpointFaces XiCurried)) ≫
            (StrictFrameMappingWeak.strictMapping C).map qXiSource := by
              simpa only [baseComparison, Category.assoc] using
                congrArg (fun t ↦ t ≫
                  (StrictFrameMappingWeak.strictMapping C).map qXiSource)
                  (xiEndpointArrow_square C)
    _ = totalComparison C ≫ resolvedArrow C := by
      rw [Category.assoc, qXi_mapping_square]
      rfl

/-- The unchanged ordered point of the actual qX source diagram. -/
def resolvedPoint (C : Coefficient) (x y : C.Obj) :
    (Δ[0] : SSet.{0}) ⟶ EndpointMappingFiber.mapping (Z := C) (source QX) :=
  EndpointMappingFiber.endpointPoint (sourceAug QXaugmentation)
    (boundaryTarget C x y)

/-- The original ordered boundary point maps to the resolved ordered
boundary point through the actual qX source component. -/
theorem endpoint_point_square (C : Coefficient) (x y : C.Obj) :
    boundaryPoint C x y ≫ baseComparison C = resolvedPoint C x y := by
  calc
    boundaryPoint C x y ≫ baseComparison C =
        (boundaryPoint C x y ≫ (xiCategoricalPairIso C).hom ≫
          (xiZeroPairIso C).hom) ≫
            (StrictFrameMappingWeak.strictMapping C).map qXiSource := by
              simp only [baseComparison, Category.assoc]
    _ = EndpointMappingFiber.endpointPoint
          (endpointCollapse XiAugmentationCurried) (boundaryTarget C x y) ≫
            (StrictFrameMappingWeak.strictMapping C).map qXiSource := by
              rw [boundaryPoint_square]
    _ = resolvedPoint C x y := by
      exact EndpointMappingFiber.endpointPoint_precomp
        (endpointCollapse XiAugmentationCurried) (boundaryTarget C x y)
        (Functor.whiskerRight qX Arrow.leftFunc)
        (sourceAug QXaugmentation) rfl

/-- The actual QX under-boundary Hom is the strict fiber of the resolved
endpoint arrow over the same ordered boundary point. -/
def resolvedFiberIso (C : Coefficient) (x y : C.Obj) :
    JTEndpointFrameComparison.homSSet QXFrame C x y ≅
      pullback (resolvedArrow C) (resolvedPoint C x y) :=
  EndpointMappingFiber.underFiberIso (structureMap QX)
    (sourceAug QXaugmentation) (boundaryTarget C x y)

/-- The specified comparison from the original chosen Xi homotopy fiber
to the literal resolved QX under-boundary Hom. -/
def xiFiberComparison (C : Coefficient) [IsFibrant C] (x y : C.Obj) :
    JTXiChosenFiber.xiHomotopyFiber C x y ⟶
      JTEndpointFrameComparison.homSSet QXFrame C x y := by
  haveI : Fibration (resolvedArrow C) :=
    JTXiEndpointMappingFibration.qXi_mapping_fibration C
  exact ChosenHomotopyFiberComparison.comparison (xiEndpointArrow C)
    (resolvedArrow C) (totalComparison C) (baseComparison C)
    (mapping_square C) (boundaryPoint C x y) (resolvedPoint C x y)
    (endpoint_point_square C x y) ≫ (resolvedFiberIso C x y).inv

/-- The generic under-boundary strict fiber projects to restriction along
the actual target coprojection of its endpoint cobase. This local lemma is
needed because the corresponding Gamma calculation is private there. -/
private theorem underFiber_fst_app {S T : SimplexCategory ⥤ Coefficient}
    (i : S ⟶ T) {B : Coefficient}
    (a : S ⟶ (Functor.const SimplexCategory).obj B)
    (C : Coefficient) (b : B ⟶ C) (k : SimplexCategory)
    (f : (EndpointMappingFiber.cobaseUnder i a).obj k ⟶ Under.mk b) :
    (((EndpointMappingFiber.underFiberIso i a b).hom ≫
        pullback.fst (EndpointMappingFiber.precomp (Z := C) i)
          (EndpointMappingFiber.endpointPoint a b)).app (op k)) f =
      (pushout.inr a i).app k ≫ f.right := by
  have hproj := (EndpointMappingFiber.span_isPullback i a b).isoPullback_hom_fst
  simp only [EndpointMappingFiber.underFiberIso, Iso.trans_hom,
    Category.assoc, EndpointMappingFiber.spanFiberIso, hproj]
  change ((EndpointMappingFiber.underSpanIso i a b).hom.app (op k) f).val = _
  let h := (IsPushout.of_hasPushout a i).map
    ((evaluation SimplexCategory Coefficient).obj k)
  change (EndpointCobaseHom.cobaseHomEquiv (i.app k) (a.app k) b
    ((Under.isoMk h.isoPushout h.inl_isoPushout_hom).inv ≫ f)).val = _
  rw [EndpointCobaseHom.cobaseHomEquiv_val, Under.comp_right,
    ← Category.assoc]
  exact congrArg (fun t ↦ t ≫ f.right) h.inr_isoPushout_inv

/-- The first projection of the qX under-boundary fiber comparison is
precomposition by qX's literal target component. -/
private theorem qX_fst_square (C : Coefficient) (x y : C.Obj) :
    (EndpointMappingFiber.underFiberIso
      (endpointFaces XiCurried) (endpointCollapse XiAugmentationCurried)
      (boundaryTarget C x y)).hom ≫
        pullback.fst
          (EndpointMappingFiber.precomp (Z := C) (endpointFaces XiCurried))
          (EndpointMappingFiber.endpointPoint
            (endpointCollapse XiAugmentationCurried)
            (boundaryTarget C x y)) ≫
        (StrictFrameMappingWeak.strictMapping C).map qXiTarget =
      JTEndpointReplacementSquare.QXToXi_precomp C x y ≫
        (resolvedFiberIso C x y).hom ≫
          pullback.fst (resolvedArrow C) (resolvedPoint C x y) := by
  ext k f
  let g := (QXToXi.app k.unop) ≫ f
  have h₁ := underFiber_fst_app (endpointFaces XiCurried)
    (endpointCollapse XiAugmentationCurried) C (boundaryTarget C x y)
    k.unop f
  have h₂ := underFiber_fst_app (structureMap QX)
    (sourceAug QXaugmentation) C (boundaryTarget C x y) k.unop g
  change (qX.app k.unop).right ≫
      (((EndpointMappingFiber.underFiberIso
        (endpointFaces XiCurried) (endpointCollapse XiAugmentationCurried)
        (boundaryTarget C x y)).hom ≫
          pullback.fst
            (EndpointMappingFiber.precomp (Z := C) (endpointFaces XiCurried))
            (EndpointMappingFiber.endpointPoint
              (endpointCollapse XiAugmentationCurried)
              (boundaryTarget C x y))).app k) f =
      (((resolvedFiberIso C x y).hom ≫
        pullback.fst (resolvedArrow C) (resolvedPoint C x y)).app k) g
  change (((resolvedFiberIso C x y).hom ≫
    pullback.fst (resolvedArrow C) (resolvedPoint C x y)).app k) g = _ at h₂
  rw [h₁, h₂]
  change (qX.app k.unop).right ≫
      ((frameInclusion
        (JTEndpointAugmentations.arrowAugmentation XiAugmentationCurried)).app
          k.unop ≫ f.right) =
    (frameInclusion QXaugmentation).app k.unop ≫
      ((QXToXi.app k.unop).right ≫ f.right)
  rw [← Category.assoc, ← Category.assoc]
  exact congrArg (fun t ↦ t ≫ f.right)
    (NatTrans.congr_app
      (JTEndpointCobaseComparison.frameInclusion_comparison qX
        QXaugmentation
        (JTEndpointAugmentations.arrowAugmentation XiAugmentationCurried)
        rfl) k.unop).symm

/-- The first leg of the Xi strict-fiber presentation is the original
ordered target map, after the checked composite-nerve row identification. -/
private theorem xiStrictFiberIso_fst (C : Coefficient) (x y : C.Obj) :
    (xiStrictFiberIso C x y).hom ≫
        pullback.fst (xiEndpointArrow C) (boundaryPoint C x y) ≫
          (xiRowMappingIso C oneIndex).hom =
      (orderedHomSSetIso XiAugmentationCurried C x y).inv ≫
        (EndpointMappingFiber.underFiberIso
          (endpointFaces XiCurried) (endpointCollapse XiAugmentationCurried)
          (boundaryTarget C x y)).hom ≫
            pullback.fst
              (EndpointMappingFiber.precomp (Z := C) (endpointFaces XiCurried))
              (EndpointMappingFiber.endpointPoint
                (endpointCollapse XiAugmentationCurried)
                (boundaryTarget C x y)) := by
  dsimp only [xiStrictFiberIso, xiPairStrictFiberIso]
  simp [Iso.trans_hom, Iso.symm_hom, Category.assoc, asIso_hom,
    pullback.map]

/-- The canonical raw-to-chosen Xi fiber inclusion followed by the actual
qX comparison equals the retained original raw-to-resolved Xi map. This
identifies the chosen comparison independently of any weak assertion about
its total or base maps. -/
theorem xiInclusion_comparison (C : Coefficient) [IsFibrant C]
    (x y : C.Obj) :
    JTXiChosenFiber.xiInclusion C x y ≫ xiFiberComparison C x y =
      JTDerivedOrderedMate.xiRawToResolved C x y := by
  haveI : Fibration (resolvedArrow C) :=
    JTXiEndpointMappingFibration.qXi_mapping_fibration C
  dsimp only [JTXiChosenFiber.xiInclusion, xiFiberComparison]
  conv_lhs =>
    rw [← Category.assoc]
    arg 1
    rw [Category.assoc]
  rw [ChosenHomotopyFiberTriangle.inclusion_comparison]
  apply (cancel_mono (resolvedFiberIso C x y).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply pullback.hom_ext
  · rw [Category.assoc,
      DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_fst]
    change (xiStrictFiberIso C x y).hom ≫
        pullback.fst (xiEndpointArrow C) (boundaryPoint C x y) ≫
          ((xiRowMappingIso C oneIndex).hom ≫
            (StrictFrameMappingWeak.strictMapping C).map qXiTarget) =
      JTDerivedOrderedMate.xiRawToResolved C x y ≫
        (resolvedFiberIso C x y).hom ≫
          pullback.fst (resolvedArrow C) (resolvedPoint C x y)
    dsimp only [JTDerivedOrderedMate.xiRawToResolved]
    calc
      _ = ((orderedHomSSetIso XiAugmentationCurried C x y).inv ≫
          (EndpointMappingFiber.underFiberIso
            (endpointFaces XiCurried) (endpointCollapse XiAugmentationCurried)
            (boundaryTarget C x y)).hom ≫
            pullback.fst
              (EndpointMappingFiber.precomp (Z := C) (endpointFaces XiCurried))
              (EndpointMappingFiber.endpointPoint
                (endpointCollapse XiAugmentationCurried)
                (boundaryTarget C x y))) ≫
          (StrictFrameMappingWeak.strictMapping C).map qXiTarget := by
            simpa only [Category.assoc] using
              congrArg (fun t ↦ t ≫
                (StrictFrameMappingWeak.strictMapping C).map qXiTarget)
                (xiStrictFiberIso_fst C x y)
      _ = _ := by
        simpa only [Category.assoc] using congrArg
          (fun t ↦ (orderedHomSSetIso XiAugmentationCurried C x y).inv ≫ t)
          (qX_fst_square C x y)
  · rw [Category.assoc,
      DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_snd]
    change (xiStrictFiberIso C x y).hom ≫
        pullback.snd (xiEndpointArrow C) (boundaryPoint C x y) =
      JTDerivedOrderedMate.xiRawToResolved C x y ≫
        (resolvedFiberIso C x y).hom ≫
          pullback.snd (resolvedArrow C) (resolvedPoint C x y)
    apply SSet.stdSimplex.objZeroIsTerminal.hom_ext

/-- The specified actual qX comparison of Xi chosen fibers is Kan weak.
This follows from the canonical strict-to-chosen inclusion and the retained
raw-to-resolved weak map, without asserting weakness of the raw total or base
row comparisons. -/
theorem xiFiberComparison_weak (C : Coefficient) [IsFibrant C]
    (x y : C.Obj) : WeakEquivalence (xiFiberComparison C x y) := by
  haveI : WeakEquivalence (JTXiChosenFiber.xiInclusion C x y) :=
    JTXiChosenFiber.xiInclusion_weak C x y
  haveI : WeakEquivalence (JTDerivedOrderedMate.xiRawToResolved C x y) :=
    JTXiDerivedMapping.xiRawToResolved_weak C x y
  exact weakEquivalence_of_precomp_of_fac (xiInclusion_comparison C x y)

/-- The chosen Xi fiber normalization is the localization of the actual
point-set qX comparison followed by the retained resolved-frame
normalization. -/
theorem xiFiberLocalization_calibration (C : Coefficient) [IsFibrant C]
    (x y : C.Obj) :
    (weakEquivalences SSet.{0}).Q.map (xiFiberComparison C x y) ≫
        (JTDerivedOrderedMate.xiLocalizationIso C x y).hom =
      (JTXiChosenFiber.xiFiberLocalizationIso C x y).hom := by
  apply (cancel_epi
    (JTXiChosenFiber.xiInclusionLocalizationIso C x y).hom).1
  simp only [JTXiChosenFiber.xiInclusionLocalizationIso,
    Localization.isoOfHom_hom]
  rw [← Category.assoc, ← Functor.map_comp, xiInclusion_comparison,
    JTXiChosenFiber.xiFiberLocalization_calibration]
  rfl

end

end DaggerModels.PartII.JTXiChosenFiberComparison
