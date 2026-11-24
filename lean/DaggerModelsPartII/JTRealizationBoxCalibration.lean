import DaggerModelsPartII.DaggerJTFrameUnderlying
import DaggerModelsPartII.DaggerJTRepresentedFrames
import DaggerModelsPartII.JTRealizationBox
import DaggerModelsPartII.JTRealizationVertices
import DaggerModelsPartII.DaggerJTRealization

/-!
# Generator calibration of the ordinary JT external box

The chosen product comparison for the actual ordinary JT realization is
computed on every coend generator. Its represented identity normalization
is proved from the unique left Kan extension's prescribed restriction.
The horizontal coefficient calculation records the actual represented
dagger action for the subsequent frame comparison.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory Simplicial DaggerModels

namespace DaggerModels.PartII.JTRealizationBoxCalibration

open DaggerJTFrameUnderlying DaggerJTAdjunction
open JTRealizationBox OrdinaryJTRealization JTRealizationGenerators
open JTRealizationVertices DaggerJTRepresentedFrames JTReversalInput

noncomputable section

private instance tensorRight_preservesColimits (K : SSet.{0}) :
    CategoryTheory.Limits.PreservesColimitsOfSize.{1, 1}
      (MonoidalCategory.tensorRight K) := by
  letI : BraidedCategory SSet.{0} := .ofCartesianMonoidalCategory
  letI : CategoryTheory.Limits.PreservesColimitsOfSize.{1, 1}
      (MonoidalCategory.tensorLeft K) := inferInstance
  exact CategoryTheory.Limits.preservesColimits_of_natIso
    (BraidedCategory.tensorLeftIsoTensorRight K)

private instance productCurried_preservesColimits_large :
    CategoryTheory.Limits.PreservesColimitsOfSize.{1, 1}
      productCurried := by
  apply CategoryTheory.Limits.preservesColimits_of_evaluation productCurried
  intro k
  let e : MonoidalCategory.tensorRight (GroupoidSimplex.parameter.obj k) ≅
      productCurried ⋙
        (evaluation SimplexCategory SSet.{0}).obj k :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro X Y f
      simp [productCurried])
  exact CategoryTheory.Limits.preservesColimits_of_natIso e

private instance realizedBoxCurried_preservesColimits_large :
    CategoryTheory.Limits.PreservesColimitsOfSize.{1, 1}
      realizedBoxCurried := by
  let e : realizedBoxCurried ≅ productCurried :=
    Functor.curry.mapIso realizationBoxIso
  exact CategoryTheory.Limits.preservesColimits_of_natIso e.symm

private instance productCurried_preservesColimits :
    CategoryTheory.Limits.PreservesColimitsOfSize.{0, 0}
      productCurried :=
  CategoryTheory.Limits.preservesSmallestColimits_of_preservesColimits _

private instance realizedBoxCurried_preservesColimits :
    CategoryTheory.Limits.PreservesColimitsOfSize.{0, 0}
      realizedBoxCurried :=
  CategoryTheory.Limits.preservesSmallestColimits_of_preservesColimits _

/-- The chosen unique extension has the prescribed restriction to the
universe-lifted Yoneda embedding. This is the Kan-extension fac equation,
before evaluating either the simplex or parameter component. -/
private theorem uniqueExtension_fac
    (L : SSet.{0} ⥤ (SimplexCategory ⥤ SSet.{0}))
    (A : SimplexCategory ⥤ (SimplexCategory ⥤ SSet.{0}))
    (e : A ≅ uliftYoneda.{0} ⋙ L)
    [CategoryTheory.Limits.PreservesColimitsOfSize.{0, 0} L] :
    e.hom ≫ Functor.whiskerLeft uliftYoneda.{0}
      (Presheaf.uniqueExtensionAlongULiftYoneda L e).hom =
        uliftYoneda.{0}.leftKanExtensionUnit A := by
  letI : L.IsLeftKanExtension e.hom :=
    Presheaf.isLeftKanExtension_of_preservesColimits L e
  change e.hom ≫ Functor.whiskerLeft uliftYoneda.{0}
      (L.descOfIsLeftKanExtension e.hom
        (uliftYoneda.{0}.leftKanExtension A)
        (𝟙 A ≫ uliftYoneda.{0}.leftKanExtensionUnit A)) = _
  simpa only [Category.id_comp] using
    L.descOfIsLeftKanExtension_fac e.hom
      (uliftYoneda.{0}.leftKanExtension A)
      (𝟙 A ≫ uliftYoneda.{0}.leftKanExtensionUnit A)

theorem representedBoxCurriedCalibration :
    Functor.whiskerLeft uliftYoneda.{0}
        (Functor.curry.mapIso realizationBoxIso).hom =
      representedRealizedBoxIso.hom ≫ representedProductIso.inv := by
  letI : PreservesColimitsOfSize.{0, 0} realizedBoxCurried :=
    preservesSmallestColimits_of_preservesColimits _
  letI : PreservesColimitsOfSize.{0, 0} productCurried :=
    preservesSmallestColimits_of_preservesColimits _
  let A := Functor.curry.obj tFunctor
  let e₁ : realizedBoxCurried ≅ uliftYoneda.{0}.leftKanExtension A :=
    Presheaf.uniqueExtensionAlongULiftYoneda
      realizedBoxCurried representedRealizedBoxIso.symm
  let e₂ : productCurried ≅ uliftYoneda.{0}.leftKanExtension A :=
    Presheaf.uniqueExtensionAlongULiftYoneda
      productCurried representedProductIso.symm
  have h₁ := uniqueExtension_fac realizedBoxCurried A
    representedRealizedBoxIso.symm
  have h₂ := uniqueExtension_fac productCurried A
    representedProductIso.symm
  change representedRealizedBoxIso.inv ≫
      Functor.whiskerLeft uliftYoneda.{0} e₁.hom = _ at h₁
  change representedProductIso.inv ≫
      Functor.whiskerLeft uliftYoneda.{0} e₂.hom = _ at h₂
  have he : (Functor.curry.mapIso realizationBoxIso).hom = e₁.hom ≫ e₂.inv := by
    apply NatTrans.ext
    funext X
    apply NatTrans.ext
    funext k
    simp [realizationBoxIso, e₁, e₂]
  rw [he]
  rw [Functor.whiskerLeft_comp]
  calc
    _ = representedRealizedBoxIso.hom ≫
        (representedRealizedBoxIso.inv ≫
          Functor.whiskerLeft uliftYoneda.{0} e₁.hom) ≫
          Functor.whiskerLeft uliftYoneda.{0} e₂.inv := by
          simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = representedRealizedBoxIso.hom ≫
        (representedProductIso.inv ≫
          Functor.whiskerLeft uliftYoneda.{0} e₂.hom) ≫
          Functor.whiskerLeft uliftYoneda.{0} e₂.inv := by
          rw [h₁, h₂]
    _ = representedRealizedBoxIso.hom ≫ representedProductIso.inv := by
          simp only [Category.assoc, ← Functor.whiskerLeft_comp,
            Iso.hom_inv_id, Functor.whiskerLeft_id', Category.comp_id]

/-- The chosen density extension agrees on a represented external box
with the original product-Yoneda comparison and co-Yoneda counit. -/
theorem representedBoxIso_hom (m k : SimplexCategory) :
    (realizationBoxIso.app (SSet.stdSimplex.obj m, k)).hom =
      realization.map (boxRepresentableIso m k).hom ≫
        (realizationRepresentableIso (m, k)).hom := by
  have h := NatTrans.congr_app
    (NatTrans.congr_app representedBoxCurriedCalibration m) k
  simpa [representedRealizedBoxIso, representedProductIso,
    realizationRepresentableIso] using h

def identityBoxCoefficient (m k : SimplexCategory) :
    (boxStandard.obj (SSet.stdSimplex.obj m, k)).obj (Opposite.op (m, k)) :=
  (SSet.stdSimplex.objEquiv.symm (𝟙 m),
    SSet.stdSimplex.objEquiv.symm (𝟙 k))

/-- The chosen box comparison sends the identity represented generator to
the identity of the literal JT product parameter. -/
theorem representedBoxIdentity (m k : SimplexCategory) :
    generator (boxStandard.obj (SSet.stdSimplex.obj m, k)) (m, k)
        (identityBoxCoefficient m k) ≫
      (realizationBoxIso.app (SSet.stdSimplex.obj m, k)).hom =
        𝟙 (tFunctor.obj (m, k)) := by
  rw [representedBoxIso_hom, ← Category.assoc,
    generator_naturality (boxRepresentableIso m k).hom]
  have hw :
      (boxRepresentableIso m k).hom.app (Opposite.op (m, k))
        (identityBoxCoefficient m k) = ULift.up (𝟙 (m, k)) := rfl
  rw [hw]
  have hid : uliftYonedaEquiv.{0}.symm (ULift.up (𝟙 (m, k))) =
      𝟙 (uliftYoneda.{0}.obj (m, k)) := by
    apply uliftYonedaEquiv.{0}.injective
    rfl
  change (realizationUnit.app (m, k) ≫
      realization.map (uliftYonedaEquiv.{0}.symm (ULift.up (𝟙 (m, k))))) ≫
      (realizationRepresentableIso (m, k)).hom = _
  rw [hid]
  simp [realizationRepresentableIso,
    Presheaf.isExtensionAlongULiftYoneda]
  rfl

/-- On every actual coend generator, the chosen box comparison evaluates
to the Yoneda map in the first coordinate and the original groupoid
parameter map in the second coordinate. -/
theorem realizationBoxIso_generator
    (X : SSet.{0}) (k m l : SimplexCategory)
    (x : X.obj (Opposite.op m))
    (β : (SSet.stdSimplex.obj k).obj (Opposite.op l)) :
    generator (boxStandard.obj (X, k)) (m, l) (x, β) ≫
      (realizationBoxIso.app (X, k)).hom =
        SSet.yonedaEquiv.symm x ⊗ₘ
          GroupoidSimplex.parameter.map (SSet.stdSimplex.objEquiv β) := by
  let u : SSet.stdSimplex.obj m ⟶ X := SSet.yonedaEquiv.symm x
  let f : l ⟶ k := SSet.stdSimplex.objEquiv β
  let t : (SSet.stdSimplex.obj m, l) ⟶ (X, k) := (u, f)
  have hw :
      (boxStandard.map t).app (Opposite.op (m, l))
        (identityBoxCoefficient m l) = (x, β) := by
    apply Prod.ext
    · change SSet.yonedaEquiv (SSet.yonedaEquiv.symm x) = x
      simp only [Equiv.apply_symm_apply]
    · change SSet.stdSimplex.objEquiv.symm
        (𝟙 l ≫ SSet.stdSimplex.objEquiv β) = β
      rw [Category.id_comp]
      simp only [Equiv.symm_apply_apply]
  have hn := generator_naturality (boxStandard.map t) (m, l)
    (identityBoxCoefficient m l)
  rw [hw] at hn
  have hnat := realizationBoxIso.hom.naturality t
  change realization.map (boxStandard.map t) ≫
      (realizationBoxIso.app (X, k)).hom =
    (realizationBoxIso.app (SSet.stdSimplex.obj m, l)).hom ≫
      (u ⊗ₘ GroupoidSimplex.parameter.map f) at hnat
  calc
    _ = generator (boxStandard.obj (SSet.stdSimplex.obj m, l)) (m, l)
          (identityBoxCoefficient m l) ≫
            realization.map (boxStandard.map t) ≫
              (realizationBoxIso.app (X, k)).hom := by
            rw [← Category.assoc, hn]
    _ = generator (boxStandard.obj (SSet.stdSimplex.obj m, l)) (m, l)
          (identityBoxCoefficient m l) ≫
            (realizationBoxIso.app (SSet.stdSimplex.obj m, l)).hom ≫
              (u ⊗ₘ GroupoidSimplex.parameter.map f) := by
            simpa only [Category.assoc] using
              congrArg (fun q ↦ generator
                (boxStandard.obj (SSet.stdSimplex.obj m, l)) (m, l)
                  (identityBoxCoefficient m l) ≫ q) hnat
    _ = u ⊗ₘ GroupoidSimplex.parameter.map f := by
          rw [← Category.assoc, representedBoxIdentity, Category.id_comp]
    _ = _ := rfl

/-- On a represented pair, the horizontal coefficient action is the
actual dagger on its restricted Yoneda simplex. The vertical coefficient
is unchanged at this stage; its inversion occurs in `tReversal_app`. -/
theorem representedHorizontalCoefficient (p : DaggerIndex)
    (m l : SimplexCategory)
    (x : (underlyingSimplex.obj p.1).obj (Opposite.op m))
    (β : (SSet.stdSimplex.obj p.2).obj (Opposite.op l)) :
    horizontalReversalCoefficient (representedTensorPair.obj p) m l (x, β) =
      (SSet.opObjEquiv
        ((reversalSimplex.obj p.1).dagger.app (Opposite.op m) x), β) := by
  rfl

/-- The ordinary product formula before transport along the dagger
represented-frame isomorphism. This is the convenient point at which to
apply the literal coend-generator reversal formula. -/
def representedBoxUnderlyingIso (p : DaggerIndex) :
    (DaggerJTRealization.daggerRealization.obj
        (representedTensorPair.obj p)).toSSet ≅ frameParameter.obj p :=
  (eqToIso DaggerJTRealization.daggerRealization_underlying).app
      (representedTensorPair.obj p) ≪≫
    realization.mapIso (representedOrdinaryBoxIso.app p) ≪≫
      realizationBoxIso.app (underlyingSimplex.obj p.1, p.2)

end

end DaggerModels.PartII.JTRealizationBoxCalibration
