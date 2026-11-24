import DaggerModelsPartII.JTXiChosenFiber
import DaggerModelsPartII.JTCompositeNativeCalibration
import DaggerModelsPartII.JTFrameGeneratorCalibration
import DaggerModelsPartII.JTEndpointMateUnder
import DaggerModelsPartII.ChosenHomotopyFiberFunctor

/-! The literal right mate on the original ordered nerve-row arrows. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTRightMateOrderedFiber

open JTRelativeReedyFrame JTActualCosimplicialFrame JTOrderedFrameMate
open JTEndpointHom JTEndpointMateUnder JTXiRowEndpoints JTGammaDerivedFiber
open DaggerNativeSSetFibrationSquareFibreWeak ChosenHomotopyFiberFunctor
open JTXiChosenFiber JTGammaStrictFiber JTActualDerivedOrderedMate

noncomputable section

private local instance : HasColimits Coefficient := daggerSimplicialCatHasColimits
private local instance : HasLimits Coefficient := daggerSimplicialCatHasLimits
private local instance : ModelCategory Coefficient :=
  DaggerActualRigidificationQuillen.modelG.{0}

/-- The original right mate evaluated in its outer-one row. -/
def mateRow (C : Coefficient) :
    xiRow C oneIndex ⟶ JTGammaRowEndpoints.gammaRow C oneIndex :=
  (JTCoendMate.rightMate.app C).app (op oneIndex)

/-- On the actual two ordered endpoint faces, precompose by the original
source of lambda. The two product identifications only change presentation. -/
def mateBase (C : Coefficient) :
    xiCategoricalZeroPairRow C ⟶ JTGammaRowEndpoints.endpointSourceRow C :=
  (xiCategoricalPairIso C).hom ≫ (xiZeroPairIso C).hom ≫
    EndpointMappingFiber.precomp (Z := C) comparisonSource

theorem matePoint (C : Coefficient) (x y : C.Obj) :
    JTXiRowEndpoints.boundaryPoint C x y ≫ mateBase C = rawPoint C x y := by
  calc
    _ = (JTXiRowEndpoints.boundaryPoint C x y ≫ (xiCategoricalPairIso C).hom ≫
        (xiZeroPairIso C).hom) ≫ EndpointMappingFiber.precomp (Z := C) comparisonSource := by
      simp only [mateBase, Category.assoc]
    _ = rawPoint C x y := ?_
  rw [boundaryPoint_square, rawPoint_eq_boundaryPoint]
  exact EndpointMappingFiber.endpointPoint_precomp
    (endpointCollapse XiAugmentationCurried) (boundaryTarget C x y)
    comparisonSource (endpointCollapse augmentation) comparison_collapse.symm

private theorem mateMappingSquare (C : Coefficient) :
    EndpointMappingFiber.precomp (Z := C) (endpointFaces XiCurried) ≫
        EndpointMappingFiber.precomp (Z := C) comparisonSource =
      EndpointMappingFiber.precomp (Z := C) comparisonOne ≫
        EndpointMappingFiber.precomp (Z := C) (endpointFaces Gamma) := by
  apply NatTrans.ext
  funext k f
  change comparisonSource.app k.unop ≫ ((endpointFaces XiCurried).app k.unop ≫ f) =
    (endpointFaces Gamma).app k.unop ≫ (comparisonOne.app k.unop ≫ f)
  rw [← Category.assoc, ← Category.assoc]
  exact congrArg (fun t ↦ t ≫ f) (NatTrans.congr_app comparison_faces k.unop).symm

/-- The coend mate evaluates by precomposition in every represented degree. -/
theorem mateComponent (C : Coefficient) (m : ReverseSimplex)
    (k : SimplexCategoryᵒᵖ) (z : (xiRow C m).obj k) :
    ((JTCoendMate.rightMate.app C).app (op m)).app k z =
      (comparison.app k.unop).app m ≫ (xiRowMappingIso C m).hom.app k z := by
  let e := xiRowMappingIso C m
  let f := e.hom.app k z
  have hz : e.inv.app k f = z := by
    exact congrFun (NatTrans.congr_app e.hom_inv_id k) z
  have hg := JTCompositeNativeCalibration.xiRowMappingIso_inv C m k.unop f
  have hmate := JTCoendMateFormula.rightMate_bidegree C m k.unop f
  rw [JTFrameGeneratorCalibration.frameGeneratorEquiv_eq_native] at hmate
  exact (congrArg (fun u ↦ ((JTCoendMate.rightMate.app C).app (op m)).app k u)
    (hz.symm.trans hg)).trans hmate

/-- The coend mate acts on the literal outer-one nerve rows. -/
theorem mateRow_mapping (C : Coefficient) :
    mateRow C ≫ (JTGammaRowEndpoints.gammaRowMappingIso C oneIndex).hom =
      (xiRowMappingIso C oneIndex).hom ≫ EndpointMappingFiber.precomp (Z := C) comparisonOne := by
  apply NatTrans.ext
  funext k z
  exact mateComponent C oneIndex k z

/-- After the coproduct Hom identification, the actual mate base map is
the ordered product of the two literal zero-row maps. -/
theorem mateBase_val (C : Coefficient) (k : SimplexCategoryᵒᵖ)
    (z : (xiCategoricalZeroPairRow C).obj k) :
    (JTGammaRowEndpoints.endpointSourceRowIso C).hom.app k ((mateBase C).app k z) =
      (((JTCoendMate.rightMate.app C).app (op JTZeroObjects.zeroIndex)).app k
        ((prod.fst : xiCategoricalZeroPairRow C ⟶ xiRow C JTZeroObjects.zeroIndex).app k z),
       ((JTCoendMate.rightMate.app C).app (op JTZeroObjects.zeroIndex)).app k
        ((prod.snd : xiCategoricalZeroPairRow C ⟶ xiRow C JTZeroObjects.zeroIndex).app k z)) := by
  let m := JTZeroObjects.zeroIndex
  let u := (prod.fst : xiCategoricalZeroPairRow C ⟶ xiRow C m).app k z
  let v := (prod.snd : xiCategoricalZeroPairRow C ⟶ xiRow C m).app k z
  let d := coprod.desc ((xiRowMappingIso C m).hom.app k u)
    ((xiRowMappingIso C m).hom.app k v)
  apply Prod.ext
  · change coprod.inl ≫ (comparisonSource.app k.unop ≫ d) =
      ((JTCoendMate.rightMate.app C).app (op m)).app k u
    rw [mateComponent]
    change coprod.inl ≫ (coprod.map ((comparison.app k.unop).app m)
      ((comparison.app k.unop).app m) ≫ d) = _
    rw [coprod.inl_map_assoc]
    change _ ≫ (coprod.inl ≫ coprod.desc _ _) = _
    rw [coprod.inl_desc]
  · change coprod.inr ≫ (comparisonSource.app k.unop ≫ d) =
      ((JTCoendMate.rightMate.app C).app (op m)).app k v
    rw [mateComponent]
    change coprod.inr ≫ (coprod.map ((comparison.app k.unop).app m)
      ((comparison.app k.unop).app m) ≫ d) = _
    rw [coprod.inr_map_assoc]
    change _ ≫ (coprod.inr ≫ coprod.desc _ _) = _
    rw [coprod.inr_desc]

theorem mateSquare (C : Coefficient) :
    xiEndpointArrow C ≫ mateBase C = mateRow C ≫ rawArrow C := by
  calc
    _ = (xiEndpointArrow C ≫ (xiCategoricalPairIso C).hom ≫
        (xiZeroPairIso C).hom) ≫ EndpointMappingFiber.precomp (Z := C) comparisonSource := by
      simp only [mateBase, Category.assoc]
    _ = _ := by
      rw [xiEndpointArrow_square, Category.assoc, mateMappingSquare,
        ← Category.assoc, ← mateRow_mapping, Category.assoc]
      rfl

/-- The actual right mate induces the chosen fiber map of its literal
endpoint square and its transported ordered point. -/
def mateChosenMap (C : Coefficient) (x y : C.Obj) :
    xiHomotopyFiber C x y ⟶ gammaHomotopyFiber C x y :=
  chosenMap (xiEndpointArrow C) (rawArrow C) (mateRow C) (mateBase C)
    (mateSquare C) (boundaryPoint C x y) (rawPoint C x y) (matePoint C x y)

private theorem mateStrict_calibration (C : Coefficient) (x y : C.Obj) :
    (xiStrictFiberIso C x y).hom ≫
        fibreMap (xiEndpointArrow C) (rawArrow C) (mateRow C) (mateBase C)
          (mateSquare C) (boundaryPoint C x y) (rawPoint C x y) (matePoint C x y) =
      orderedMate C x y ≫ (gammaStrictFiberIso C x y).hom := by
  apply pullback.hom_ext
  · simp only [Category.assoc, fibreMap_fst]
    apply NatTrans.ext
    funext k z
    change (mateRow C).app k
        (((xiStrictFiberIso C x y).hom ≫ pullback.fst (xiEndpointArrow C)
          (boundaryPoint C x y)).app k z) =
      (((gammaStrictFiberIso C x y).hom ≫ pullback.fst (rawArrow C)
        (rawPoint C x y)).app k) ((orderedMate C x y).app k z)
    have hx := xiStrictFiberIso_fst_app C x y k.unop z
    have hg := gammaStrictFiberIso_fst_app C x y k.unop ((orderedMate C x y).app k z)
    rw [hx, hg, JTCompositeNativeCalibration.xiRowMappingIso_inv]
    have hmate := JTOrderedFrameMate.rightMate_ordered_bidegree C x y k.unop z
    rw [JTFrameGeneratorCalibration.frameGeneratorEquiv_eq_native] at hmate
    exact hmate
  · exact SSet.stdSimplex.objZeroIsTerminal.hom_ext _ _

/-- The chosen right-mate map restricts to the previously verified ordered
mate followed by the canonical Gamma inclusion. -/
theorem mateChosenMap_calibration (C : Coefficient) (x y : C.Obj) :
    xiInclusion C x y ≫ mateChosenMap C x y = actualToGammaFiber C x y := by
  dsimp only [xiInclusion, mateChosenMap, actualToGammaFiber, gammaInclusion]
  rw [Category.assoc, inclusion_chosenMap, ← Category.assoc, mateStrict_calibration,
    Category.assoc]

/-- The actual nerve-row right mate is weak on the original chosen fibers
over each specified ordered pair in a fibrant coefficient. -/
theorem mateChosenMap_weak (C : Coefficient) [IsFibrant C] (x y : C.Obj) :
    WeakEquivalence (mateChosenMap C x y) := by
  haveI : WeakEquivalence (xiInclusion C x y) := xiInclusion_weak C x y
  haveI : WeakEquivalence (actualToGammaFiber C x y) := actualToGammaFiber_weak C x y
  exact weakEquivalence_of_precomp_of_fac (mateChosenMap_calibration C x y)

end

end DaggerModels.PartII.JTRightMateOrderedFiber
