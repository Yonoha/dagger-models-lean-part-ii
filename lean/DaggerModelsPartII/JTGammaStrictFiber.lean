import DaggerModelsPartII.JTGammaDerivedFiber
import DaggerModelsPartII.JTDerivedOrderedMate
import DaggerModelsPartII.ChosenHomotopyFiberTriangle

/-!
# The original Gamma ordered Hom as the strict endpoint fiber

The original ordered equations define the strict fiber of the literal Gamma
endpoint arrow at the original ordered point. Its canonical map to the chosen
homotopy fiber composes to the already checked raw-to-resolved comparison.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTGammaStrictFiber

open JTRelativeReedyFrame JTActualCosimplicialFrame JTEndpointHom
open JTOrderedFrameMate JTGammaRowEndpoints JTGammaDerivedFiber
open JTDerivedOrderedAction JTEndpointArrowReplacement JTEndpointAugmentations

noncomputable section

private local instance : HasLimits Coefficient := daggerSimplicialCatHasLimits
private local instance : HasColimits Coefficient := daggerSimplicialCatHasColimits
private local instance : ModelCategory Coefficient :=
  DaggerActualRigidificationQuillen.modelG.{0}

/-- Reparametrize the source of the raw mapping arrow by the exact
`gammaRowMappingIso`, retaining the original boundary point. -/
private def rawPullbackIso (C : Coefficient) (x y : C.Obj) :
    pullback
      (EndpointMappingFiber.precomp (Z := C) (endpointFaces Gamma))
      (EndpointMappingFiber.endpointPoint
        (endpointCollapse augmentation) (boundaryTarget C x y)) ≅
      pullback (rawArrow C) (rawPoint C x y) := by
  let e := gammaRowMappingIso C oneIndex
  let q := EndpointMappingFiber.precomp (Z := C) (endpointFaces Gamma)
  let b := EndpointMappingFiber.endpointPoint
    (endpointCollapse augmentation) (boundaryTarget C x y)
  have h₁ : q ≫ (𝟙 _) = e.inv ≫ rawArrow C := by
    dsimp only [rawArrow, JTGammaRowEndpoints.gammaEndpointArrow]
    rw [Category.comp_id, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have h₂ : b ≫ (𝟙 _) = (𝟙 _) ≫ rawPoint C x y := by
    dsimp only [rawPoint, b]
    simpa only [Category.id_comp, Category.comp_id] using
      (rawPoint_eq_boundaryPoint C x y).symm
  exact asIso (pullback.map q b (rawArrow C) (rawPoint C x y)
    e.inv (𝟙 _) (𝟙 _) h₁ h₂)

private theorem rawPullbackIso_fst (C : Coefficient) (x y : C.Obj) :
    (rawPullbackIso C x y).hom ≫
        pullback.fst (rawArrow C) (rawPoint C x y) =
      pullback.fst
          (EndpointMappingFiber.precomp (Z := C) (endpointFaces Gamma))
          (EndpointMappingFiber.endpointPoint
            (endpointCollapse augmentation) (boundaryTarget C x y)) ≫
        (gammaRowMappingIso C oneIndex).inv := by
  simp only [rawPullbackIso, asIso_hom, pullback.map,
    pullback.lift_fst]

/-- The original ordered Gamma Hom is the strict pullback of the exact raw
endpoint mapping arrow over its specified ordered point. -/
def gammaStrictFiberIso (C : Coefficient) (x y : C.Obj) :
    GammaOrdered C x y ≅ pullback (rawArrow C) (rawPoint C x y) :=
  (orderedHomSSetIso augmentation C x y).symm ≪≫
    EndpointMappingFiber.underFiberIso
      (endpointFaces Gamma) (endpointCollapse augmentation)
      (boundaryTarget C x y) ≪≫ rawPullbackIso C x y

/-- The literal Gamma ordered Hom maps canonically into the chosen
homotopy fiber of its original endpoint arrow, without asserting that this
inclusion is weak. -/
def gammaInclusion (C : Coefficient) (x y : C.Obj) :
    GammaOrdered C x y ⟶ gammaHomotopyFiber C x y :=
  (gammaStrictFiberIso C x y).hom ≫
    ChosenHomotopyFiberTriangle.inclusion (rawArrow C) (rawPoint C x y)

private theorem ordered_fst_app (C : Coefficient) (x y : C.Obj)
    (k : SimplexCategory) (z : (GammaOrdered C x y).obj (op k)) :
    (((orderedHomSSetIso augmentation C x y).inv ≫
      (EndpointMappingFiber.underFiberIso
        (endpointFaces Gamma) (endpointCollapse augmentation)
        (boundaryTarget C x y)).hom ≫
      pullback.fst
        (EndpointMappingFiber.precomp (Z := C) (endpointFaces Gamma))
        (EndpointMappingFiber.endpointPoint (endpointCollapse augmentation)
          (boundaryTarget C x y))).app (op k)) z = z.val := by
  let f := (orderedHomSSetIso augmentation C x y).inv.app (op k) z
  have h := EndpointMappingFiber.underFiberIso_hom_fst_app (endpointFaces Gamma)
    (endpointCollapse augmentation) (boundaryTarget C x y) k f
  change (((EndpointMappingFiber.underFiberIso
    (endpointFaces Gamma) (endpointCollapse augmentation)
    (boundaryTarget C x y)).hom ≫ pullback.fst
      (EndpointMappingFiber.precomp (Z := C) (endpointFaces Gamma))
      (EndpointMappingFiber.endpointPoint (endpointCollapse augmentation)
        (boundaryTarget C x y))).app (op k)) f = z.val
  rw [h]
  have ho := orderedHomEquiv_val augmentation C x y k f
  have hs : orderedHomEquiv augmentation C x y k f = z := by
    exact (orderedHomEquiv augmentation C x y k).apply_symm_apply z
  exact ho.symm.trans (congrArg Subtype.val hs)


/-- The literal strict Gamma fiber projects to the underlying ordered Hom
element in the original frame-nerve row. -/
theorem gammaStrictFiberIso_fst_app (C : Coefficient) (x y : C.Obj)
    (k : SimplexCategory) (f : (GammaOrdered C x y).obj (op k)) :
    (((gammaStrictFiberIso C x y).hom ≫
      pullback.fst (rawArrow C) (rawPoint C x y)).app (op k)) f = f.val := by
  simp only [gammaStrictFiberIso, Iso.trans_hom, Category.assoc, rawPullbackIso_fst]
  exact ordered_fst_app C x y k f

private theorem qG_fst_square (C : Coefficient) (x y : C.Obj) :
    (EndpointMappingFiber.underFiberIso
      (endpointFaces Gamma) (endpointCollapse augmentation)
      (boundaryTarget C x y)).hom ≫
        pullback.fst
          (EndpointMappingFiber.precomp (Z := C) (endpointFaces Gamma))
          (EndpointMappingFiber.endpointPoint (endpointCollapse augmentation)
            (boundaryTarget C x y)) ≫
        (StrictFrameMappingWeak.strictMapping C).map qGammaTarget =
      JTEndpointReplacementSquare.QGToGamma_precomp C x y ≫
        (resolvedFiberIso C x y).hom ≫
          pullback.fst (resolvedArrow C) (resolvedPoint C x y) := by
  ext k f
  let g := (JTEndpointReplacementSquare.QGToGamma.app k.unop) ≫ f
  have h₁ := EndpointMappingFiber.underFiberIso_hom_fst_app (endpointFaces Gamma)
    (endpointCollapse augmentation) (boundaryTarget C x y) k.unop f
  have h₂ := EndpointMappingFiber.underFiberIso_hom_fst_app (JTEndpointCobaseAugmentations.structureMap QG)
    (JTEndpointCobaseAugmentations.sourceAug QGaugmentation)
    (boundaryTarget C x y) k.unop g
  change (qG.app k.unop).right ≫
      (((EndpointMappingFiber.underFiberIso
        (endpointFaces Gamma) (endpointCollapse augmentation)
        (boundaryTarget C x y)).hom ≫ pullback.fst
          (EndpointMappingFiber.precomp (Z := C) (endpointFaces Gamma))
          (EndpointMappingFiber.endpointPoint (endpointCollapse augmentation)
            (boundaryTarget C x y))).app k) f =
      (((resolvedFiberIso C x y).hom ≫
        pullback.fst (resolvedArrow C) (resolvedPoint C x y)).app k) g
  change (((resolvedFiberIso C x y).hom ≫
    pullback.fst (resolvedArrow C) (resolvedPoint C x y)).app k) g = _ at h₂
  rw [h₁, h₂]
  change (qG.app k.unop).right ≫
      ((JTEndpointCobaseAugmentations.frameInclusion
        (arrowAugmentation augmentation)).app k.unop ≫ f.right) =
    (JTEndpointCobaseAugmentations.frameInclusion QGaugmentation).app k.unop ≫
      ((JTEndpointReplacementSquare.QGToGamma.app k.unop).right ≫ f.right)
  rw [← Category.assoc, ← Category.assoc]
  exact congrArg (fun t ↦ t ≫ f.right)
    (NatTrans.congr_app
      (JTEndpointCobaseComparison.frameInclusion_comparison qG
        QGaugmentation (arrowAugmentation augmentation) rfl) k.unop).symm

/-- The canonical strict-to-chosen inclusion followed by the existing
chosen-to-resolved comparison is the original raw-to-resolved map. -/
theorem gammaInclusion_comparison (C : Coefficient) [IsFibrant C]
    (x y : C.Obj) :
    gammaInclusion C x y ≫ gammaFiberComparison C x y =
      JTDerivedOrderedMate.gammaRawToResolved C x y := by
  haveI : Fibration (resolvedArrow C) := qGamma_mapping_fibration C
  dsimp only [gammaInclusion, gammaFiberComparison]
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
    change (gammaStrictFiberIso C x y).hom ≫
        pullback.fst (rawArrow C) (rawPoint C x y) ≫
          ((gammaRowMappingIso C oneIndex).hom ≫
            (StrictFrameMappingWeak.strictMapping C).map qGammaTarget) =
      JTDerivedOrderedMate.gammaRawToResolved C x y ≫
        (resolvedFiberIso C x y).hom ≫
          pullback.fst (resolvedArrow C) (resolvedPoint C x y)
    dsimp only [gammaStrictFiberIso, JTDerivedOrderedMate.gammaRawToResolved]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [reassoc_of% rawPullbackIso_fst C x y]
    simp only [Iso.inv_hom_id_assoc]
    exact congrArg (fun t ↦ (orderedHomSSetIso augmentation C x y).inv ≫ t)
      (qG_fst_square C x y)
  · rw [Category.assoc,
      DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_snd]
    change (gammaStrictFiberIso C x y).hom ≫
        pullback.snd (rawArrow C) (rawPoint C x y) =
      JTDerivedOrderedMate.gammaRawToResolved C x y ≫
        (resolvedFiberIso C x y).hom ≫
          pullback.snd (resolvedArrow C) (resolvedPoint C x y)
    apply SSet.stdSimplex.objZeroIsTerminal.hom_ext

end

end DaggerModels.PartII.JTGammaStrictFiber
