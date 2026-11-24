import DaggerModelsPartII.OrdinaryJTRealization
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

/-!
# The ordinary Joyal--Tierney external box

The external box is the literal bisimplicial presheaf with degree `(m,l)`
equal to `X_m × K_l`. Its realization against the groupoid-completed simplex
is compared with `X × J^k` using the density of the standard simplices.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory DaggerModels

namespace DaggerModels.PartII.JTRealizationBox

open OrdinaryJTRealization

noncomputable section

/-- First projection from the opposite of the product index. -/
def firstProjection : Indexᵒᵖ ⥤ SimplexCategoryᵒᵖ :=
  (CategoryTheory.prodOpEquiv (C := SimplexCategory)
    (D := SimplexCategory)).functor ⋙
      CategoryTheory.Prod.fst _ _

/-- Second projection from the opposite of the product index. -/
def secondProjection : Indexᵒᵖ ⥤ SimplexCategoryᵒᵖ :=
  (CategoryTheory.prodOpEquiv (C := SimplexCategory)
    (D := SimplexCategory)).functor ⋙
      CategoryTheory.Prod.snd _ _

/-- Pull back a simplicial set to the first bisimplicial direction. -/
def pullFirst : SSet.{0} ⥤ BiPresheaf :=
  (Functor.whiskeringLeft _ _ _).obj firstProjection

/-- Pull back a simplicial set to the second bisimplicial direction. -/
def pullSecond : SSet.{0} ⥤ BiPresheaf :=
  (Functor.whiskeringLeft _ _ _).obj secondProjection

/-- The external box, functorial in both simplicial sets. -/
def boxFunctor : SSet.{0} × SSet.{0} ⥤ BiPresheaf :=
  (pullFirst.prod pullSecond) ⋙ MonoidalCategory.tensor BiPresheaf

/-- The manuscript's `X ⊠ Δ[k]`, functorial in `X` and `[k]`. -/
def boxStandard : SSet.{0} × SimplexCategory ⥤ BiPresheaf :=
  ((𝟭 SSet.{0}).prod SSet.stdSimplex.{0}) ⋙ boxFunctor

@[simp] theorem boxStandard_obj_obj (X : SSet.{0})
    (m k l : SimplexCategory) :
    ((boxStandard.obj (X, k)).obj (op (m, l))) =
      (X.obj (op m) × (SSet.stdSimplex.obj k).obj (op l)) := rfl

/-- Product Yoneda on a pair of standard simplices. The component sends
`(f, g)` to the pair morphism `(f, g)` in the product simplex category. -/
def boxRepresentableIso (m k : SimplexCategory) :
    boxStandard.obj (SSet.stdSimplex.obj m, k) ≅
      uliftYoneda.{0}.obj (m, k) :=
  NatIso.ofComponents
    (fun p =>
      (show (boxStandard.obj (SSet.stdSimplex.obj m, k)).obj p ≃
          (uliftYoneda.{0}.obj (m, k)).obj p from
        { toFun := fun x => ULift.up (x.1.down, x.2.down)
          invFun := fun x => (ULift.up x.down.1, ULift.up x.down.2)
          left_inv := by intro x; cases x; rfl
          right_inv := by intro x; cases x; rfl }).toIso)
    (by intro p q f; ext x; rfl)

/-- The preceding product-Yoneda isomorphism varies naturally in both
standard-simplex parameters. -/
def boxRepresentableNatIso :
    (SSet.stdSimplex.{0}.prod (𝟭 SimplexCategory)) ⋙ boxStandard ≅
      uliftYoneda.{0} :=
  NatIso.ofComponents
    (fun p => boxRepresentableIso p.1 p.2)
    (by intro p q f; ext r x; rfl)

/-- The realized external box, curried in its simplicial-set variable. -/
def realizedBoxCurried : SSet.{0} ⥤ SimplexCategory ⥤ SSet.{0} :=
  Functor.curry.obj (boxStandard ⋙ realization)

/-- Pointwise product with the groupoid-completed simplex, curried in `X`. -/
def productCurried : SSet.{0} ⥤ SimplexCategory ⥤ SSet.{0} :=
  Functor.curry.obj
    (((𝟭 SSet.{0}).prod GroupoidSimplex.parameter) ⋙
      MonoidalCategory.tensor SSet.{0})

/-- On represented `X = Δ[m]`, co-Yoneda compares realization with the
original two-variable JT parameter, naturally in `m` and `k`. -/
def representedRealizedBoxIso :
    uliftYoneda.{0} ⋙ realizedBoxCurried ≅
      Functor.curry.obj tFunctor := by
  let e :
      (SSet.stdSimplex.{0}.prod (𝟭 SimplexCategory)) ⋙
          boxStandard ⋙ realization ≅ tFunctor :=
    Functor.isoWhiskerRight boxRepresentableNatIso realization ≪≫
      Presheaf.isExtensionAlongULiftYoneda tFunctor
  let c : uliftYoneda.{0} ⋙ realizedBoxCurried ≅
      Functor.curry.obj
        ((SSet.stdSimplex.{0}.prod (𝟭 SimplexCategory)) ⋙
          boxStandard ⋙ realization) :=
    NatIso.ofComponents (fun _ => NatIso.ofComponents (fun _ => Iso.refl _))
  exact c ≪≫ Functor.curry.mapIso e

/-- On standard simplices, product with `J^k` is the same two-variable
JT parameter, with its functoriality in both indices. -/
def representedProductIso :
    uliftYoneda.{0} ⋙ productCurried ≅
      Functor.curry.obj tFunctor :=
  NatIso.ofComponents (fun _ => NatIso.ofComponents (fun _ => Iso.refl _))

private instance tensorRight_preservesColimits_bi (K : BiPresheaf) :
    PreservesColimitsOfSize.{1, 1} (tensorRight K) := by
  letI : BraidedCategory BiPresheaf := .ofCartesianMonoidalCategory
  letI : PreservesColimitsOfSize.{1, 1} (tensorLeft K) := inferInstance
  exact preservesColimits_of_natIso
    (BraidedCategory.tensorLeftIsoTensorRight K)

private instance pullFirst_preservesColimits :
    PreservesColimitsOfSize.{1, 1} pullFirst := by
  exact (firstProjection.ranAdjunction (Type)).leftAdjoint_preservesColimits

private instance boxSlice_preservesColimits (k : SimplexCategory) :
    PreservesColimitsOfSize.{1, 1}
      (CategoryTheory.Prod.sectL SSet.{0} k ⋙ boxStandard) := by
  let e : pullFirst ⋙ tensorRight (pullSecond.obj (SSet.stdSimplex.obj k)) ≅
      CategoryTheory.Prod.sectL SSet.{0} k ⋙ boxStandard :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro X Y f
      simp [boxStandard, boxFunctor, pullFirst, pullSecond]
      change (pullFirst.map f) ▷ (pullSecond.obj _) =
        (pullFirst.map f) ⊗ₘ (pullSecond.map (𝟙 _))
      rw [pullSecond.map_id, tensorHom_id])
  exact preservesColimits_of_natIso e

private instance realizedBoxCurried_preservesColimits :
    PreservesColimitsOfSize.{1, 1} realizedBoxCurried := by
  apply preservesColimits_of_evaluation realizedBoxCurried
  intro k
  change PreservesColimitsOfSize.{1, 1}
    ((CategoryTheory.Prod.sectL SSet.{0} k ⋙ boxStandard) ⋙ realization)
  letI : PreservesColimitsOfSize.{1, 1} realization :=
    realizationNerveAdjunction.leftAdjoint_preservesColimits
  infer_instance

private instance tensorRight_preservesColimits_sset (K : SSet.{0}) :
    PreservesColimitsOfSize.{1, 1} (tensorRight K) := by
  letI : BraidedCategory SSet.{0} := .ofCartesianMonoidalCategory
  letI : PreservesColimitsOfSize.{1, 1} (tensorLeft K) := inferInstance
  exact preservesColimits_of_natIso
    (BraidedCategory.tensorLeftIsoTensorRight K)

private instance productCurried_preservesColimits :
    PreservesColimitsOfSize.{1, 1} productCurried := by
  apply preservesColimits_of_evaluation productCurried
  intro k
  let e : tensorRight (GroupoidSimplex.parameter.obj k) ≅
      productCurried ⋙ (evaluation SimplexCategory SSet.{0}).obj k :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro X Y f
      simp [productCurried])
  exact preservesColimits_of_natIso e

/-- The ordinary JT comparison `t_!(X ⊠ Δ[k]) ≅ X × J^k`, jointly natural
in the simplicial set `X` and the simplex category parameter `[k]`. -/
def realizationBoxIso :
    boxStandard ⋙ realization ≅
      ((𝟭 SSet.{0}).prod GroupoidSimplex.parameter) ⋙
        MonoidalCategory.tensor SSet.{0} := by
  letI : PreservesColimitsOfSize.{0, 0} realizedBoxCurried :=
    preservesSmallestColimits_of_preservesColimits realizedBoxCurried
  letI : PreservesColimitsOfSize.{0, 0} productCurried :=
    preservesSmallestColimits_of_preservesColimits productCurried
  let a := Functor.curry.obj tFunctor
  let e₁ := Presheaf.uniqueExtensionAlongULiftYoneda
    realizedBoxCurried representedRealizedBoxIso.symm
  let e₂ := Presheaf.uniqueExtensionAlongULiftYoneda
    productCurried representedProductIso.symm
  let e : realizedBoxCurried ≅ productCurried := e₁ ≪≫ e₂.symm
  exact (eqToIso (Functor.uncurry_obj_curry_obj
    (boxStandard ⋙ realization))).symm ≪≫
      Functor.uncurry.mapIso e ≪≫
        eqToIso (Functor.uncurry_obj_curry_obj
          (((𝟭 SSet.{0}).prod GroupoidSimplex.parameter) ⋙
            MonoidalCategory.tensor SSet.{0}))

end

end DaggerModels.PartII.JTRealizationBox
