import DaggerModelsPartII.OrdinaryJTRealization
import DaggerModelsPartII.JTParameterZero
import TopCatModelCategory.SSet.StandardSimplex
import Mathlib.CategoryTheory.Products.Basic

/-!
# The literal first row of the ordinary JT right nerve

The degree-zero groupoid parameter is terminal. Consequently the first row
of the actual restricted-Yoneda right adjoint is naturally the original
simplicial set, including its universe lift and both naturality directions.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open CartesianMonoidalCategory

namespace DaggerModels.PartII.OrdinaryJTFirstRowIdentity

open OrdinaryJTRealization

noncomputable section

/-- Restrict a literal bisimplicial presheaf to its second degree zero. -/
def firstRow : BiPresheaf ⥤ SSet.{0} :=
  (Functor.whiskeringLeft _ _ _).obj
    (CategoryTheory.Prod.sectL SimplexCategory ⦋0⦌).op

/-- The actual JT weight in second degree zero is the horizontal simplex. -/
def zeroWeightIso (m : SimplexCategory) :
    tFunctor.obj (m, ⦋0⦌) ≅ SSet.stdSimplex.obj m where
  hom := fst _ _
  inv := lift (𝟙 _) (JTParameterZero.parameterZeroIsTerminal.from _)
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · exact JTParameterZero.parameterZeroIsTerminal.hom_ext _ _
  inv_hom_id := by simp

/-- The first projection respects all horizontal simplex operators. -/
theorem zeroWeightIso_natural {m n : SimplexCategory} (f : m ⟶ n) :
    tFunctor.map (f, 𝟙 ⦋0⦌) ≫ (zeroWeightIso n).hom =
      (zeroWeightIso m).hom ≫ SSet.stdSimplex.map f := by
  change (SSet.stdSimplex.map f ⊗ₘ GroupoidSimplex.parameter.map (𝟙 ⦋0⦌)) ≫
      fst _ _ = fst _ _ ≫ SSet.stdSimplex.map f
  exact tensorHom_fst _ _

/-- The inverse weight comparison has the same horizontal naturality. -/
theorem zeroWeightIso_natural_inv {m n : SimplexCategory} (f : m ⟶ n) :
    SSet.stdSimplex.map f ≫ (zeroWeightIso n).inv =
      (zeroWeightIso m).inv ≫ tFunctor.map (f, 𝟙 ⦋0⦌) := by
  calc
    SSet.stdSimplex.map f ≫ (zeroWeightIso n).inv =
        (zeroWeightIso m).inv ≫
          ((zeroWeightIso m).hom ≫ SSet.stdSimplex.map f) ≫
            (zeroWeightIso n).inv := by simp [Category.assoc]
    _ = (zeroWeightIso m).inv ≫
          (tFunctor.map (f, 𝟙 ⦋0⦌) ≫ (zeroWeightIso n).hom) ≫
            (zeroWeightIso n).inv := by rw [zeroWeightIso_natural f]
    _ = (zeroWeightIso m).inv ≫ tFunctor.map (f, 𝟙 ⦋0⦌) := by simp

/-- The first row of the actual ordinary JT right nerve, objectwise. -/
def firstRowNerveIsoAt (X : SSet.{0}) : firstRow.obj (nerve.obj X) ≅ X where
  hom := {
    app := fun m h ↦
      SSet.yonedaEquiv ((zeroWeightIso m.unop).inv ≫ h.down)
    naturality := by
      intro a b f
      funext h
      change SSet.yonedaEquiv
          ((zeroWeightIso b.unop).inv ≫
            tFunctor.map (f.unop, 𝟙 ⦋0⦌) ≫ h.down) =
        X.map f (SSet.yonedaEquiv ((zeroWeightIso a.unop).inv ≫ h.down))
      calc
        _ = SSet.yonedaEquiv
            (SSet.stdSimplex.map f.unop ≫
              ((zeroWeightIso a.unop).inv ≫ h.down)) := by
                rw [← Category.assoc, ← zeroWeightIso_natural_inv f.unop]
                simp only [Category.assoc]
        _ = X.map f (SSet.yonedaEquiv
            ((zeroWeightIso a.unop).inv ≫ h.down)) := by
              simpa only [Category.assoc] using (SSet.yonedaEquiv_map_comp f.unop
                ((zeroWeightIso a.unop).inv ≫ h.down)) }
  inv := {
    app := fun m h ↦
      ULift.up ((zeroWeightIso m.unop).hom ≫ SSet.yonedaEquiv.symm h)
    naturality := by
      intro a b f
      funext h
      change ULift.up ((zeroWeightIso b.unop).hom ≫
          SSet.yonedaEquiv.symm (X.map f h)) =
        ULift.up (tFunctor.map (f.unop, 𝟙 ⦋0⦌) ≫
          ((zeroWeightIso a.unop).hom ≫ SSet.yonedaEquiv.symm h))
      congr 1
      have hmap : SSet.yonedaEquiv.symm (X.map f h) =
          SSet.stdSimplex.map f.unop ≫ SSet.yonedaEquiv.symm h := by
        simpa only using SSet.yonedaEquiv_symm_map f.unop h
      calc
        (zeroWeightIso b.unop).hom ≫ SSet.yonedaEquiv.symm (X.map f h) =
            ((zeroWeightIso b.unop).hom ≫ SSet.stdSimplex.map f.unop) ≫
              SSet.yonedaEquiv.symm h := by
                rw [hmap]
                simp only [Category.assoc]
        _ = (tFunctor.map (f.unop, 𝟙 ⦋0⦌) ≫
              (zeroWeightIso a.unop).hom) ≫ SSet.yonedaEquiv.symm h := by
                rw [zeroWeightIso_natural f.unop]
        _ = tFunctor.map (f.unop, 𝟙 ⦋0⦌) ≫
              ((zeroWeightIso a.unop).hom ≫ SSet.yonedaEquiv.symm h) :=
                Category.assoc _ _ _ }
  hom_inv_id := by
    apply NatTrans.ext
    funext m h
    apply ULift.ext
    change (zeroWeightIso m.unop).hom ≫
        SSet.yonedaEquiv.symm
          (SSet.yonedaEquiv ((zeroWeightIso m.unop).inv ≫ h.down)) = h.down
    simp
  inv_hom_id := by
    apply NatTrans.ext
    funext m h
    change SSet.yonedaEquiv
      ((zeroWeightIso m.unop).inv ≫
        (zeroWeightIso m.unop).hom ≫ SSet.yonedaEquiv.symm h) = h
    simp

/-- This isomorphism is natural in the original ordinary simplicial set. -/
def nerveFirstRowIso : nerve ⋙ firstRow ≅ 𝟭 SSet.{0} :=
  NatIso.ofComponents firstRowNerveIsoAt (by
    intro X Y f
    apply NatTrans.ext
    funext m h
    change SSet.yonedaEquiv
        ((zeroWeightIso m.unop).inv ≫ (h.down ≫ f)) =
      f.app _ (SSet.yonedaEquiv ((zeroWeightIso m.unop).inv ≫ h.down))
    rw [← Category.assoc, SSet.yonedaEquiv_comp])

#print axioms firstRow
#print axioms zeroWeightIso
#print axioms nerveFirstRowIso

end
end DaggerModels.PartII.OrdinaryJTFirstRowIdentity
