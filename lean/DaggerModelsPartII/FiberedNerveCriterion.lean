import NativeDualTheoremA
import DaggerModelsPartII.FiniteWeakCover
import NativeAllCofibrantLocalizationSaturation
import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.CategoryTheory.FiberedCategory.Fiber

/-! Dual Quillen Theorem A for a functor with actual Cartesian restrictions. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra
open DaggerSSetGluing DaggerOriginalProductGadget DaggerNerveHomotopy
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.FiberedNerveCriterion

open Functor IsHomLift IsStronglyCartesian

noncomputable section

variable {C B : Type} [SmallCategory C] [SmallCategory B]
variable (p : C ⥤ B) [p.IsFibered] (b : B)

private abbrev F := Fiber p b

private def fiberObject (X : StructuredArrow b p) : F p b :=
  ⟨Functor.IsPreFibered.pullbackObj rfl X.hom,
    domain_eq p X.hom (Functor.IsPreFibered.pullbackMap rfl X.hom)⟩

private def liftTo (X : StructuredArrow b p) : (fiberObject p b X).val ⟶ X.right :=
  Functor.IsPreFibered.pullbackMap rfl X.hom

private instance cartesianLift (X : StructuredArrow b p) :
    p.IsStronglyCartesian X.hom (liftTo p b X) :=
  letI : p.IsCartesian X.hom (liftTo p b X) :=
    Functor.IsPreFibered.pullbackMap.IsCartesian rfl X.hom
  Functor.IsFibered.isStronglyCartesian_of_isCartesian p X.hom _

private def factor {X Y : StructuredArrow b p} (f : X ⟶ Y) :
    (fiberObject p b X).val ⟶ (fiberObject p b Y).val := by
  haveI : IsHomLift p (X.hom ≫ p.map f.right) (liftTo p b X ≫ f.right) :=
    IsHomLift.comp p X.hom (p.map f.right) _ _
  exact IsStronglyCartesian.map p Y.hom (liftTo p b Y) (g := 𝟙 b)
    ((StructuredArrow.w f).trans (Category.id_comp _).symm) (liftTo p b X ≫ f.right)

private theorem factor_fac {X Y : StructuredArrow b p} (f : X ⟶ Y) :
    factor p b f ≫ liftTo p b Y = liftTo p b X ≫ f.right :=
  IsStronglyCartesian.fac _ _ _ _ _

private instance factor_lift {X Y : StructuredArrow b p} (f : X ⟶ Y) :
    IsHomLift p (𝟙 b) (factor p b f) :=
  IsStronglyCartesian.map_isHomLift _ _ _ _ _

private def retract : StructuredArrow b p ⥤ F p b where
  obj := fiberObject p b
  map f := ⟨factor p b f, inferInstance⟩
  map_id X := by
    apply Subtype.ext
    change factor p b (𝟙 X) = 𝟙 (fiberObject p b X).val
    letI : IsHomLift p (𝟙 b) (𝟙 (fiberObject p b X).val) :=
      IsHomLift.id (fiberObject p b X).property
    apply IsStronglyCartesian.ext p X.hom (liftTo p b X) (𝟙 b)
    rw [factor_fac, StructuredArrow.id_right, Category.comp_id, Category.id_comp]
  map_comp {X Y Z} f g := by
    apply Subtype.ext
    change factor p b (f ≫ g) = factor p b f ≫ factor p b g
    letI : IsHomLift p (𝟙 b) (factor p b f ≫ factor p b g) := by
      simpa only [Category.id_comp] using
        (IsHomLift.comp p (𝟙 b) (𝟙 b) (factor p b f) (factor p b g))
    apply IsStronglyCartesian.ext p Z.hom (liftTo p b Z) (𝟙 b)
    rw [factor_fac, Category.assoc, factor_fac, ← Category.assoc, factor_fac]
    exact (Category.assoc _ _ _).symm

private def inclusion : F p b ⥤ StructuredArrow b p where
  obj X := StructuredArrow.mk (eqToHom X.property.symm)
  map {X Y} f := StructuredArrow.homMk f.val (by
    letI : IsHomLift p (𝟙 b) f.val := f.property
    have h := IsHomLift.fac' p (𝟙 b) f.val
    change eqToHom X.property.symm ≫ p.map f.val = eqToHom Y.property.symm
    rw [h]
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp])
  map_id _ := rfl
  map_comp _ _ := rfl

private def deformation : retract p b ⋙ inclusion p b ⟶ 𝟭 (StructuredArrow b p) where
  app X := StructuredArrow.homMk (liftTo p b X) (by
    have h := IsHomLift.fac' p X.hom (liftTo p b X)
    change eqToHom (fiberObject p b X).property.symm ≫ p.map (liftTo p b X) = X.hom
    rw [h]
    simp only [eqToHom_refl, Category.comp_id, eqToHom_trans_assoc, Category.id_comp])
  naturality {_ _} f := StructuredArrow.hom_ext _ _ (factor_fac p b f)

set_option maxHeartbeats 400000 in
/-- If the original fiber is weakly contractible, so is the structured comma. -/
theorem comma_point_GW (h : GW (pointMap (nerve (F p b)))) :
    GW (pointMap (nerve (StructuredArrow b p))) := by
  let X := nerve (StructuredArrow b p)
  let Y := nerve (F p b)
  let L := (weakEquivalences SSet.{0}).Q
  let r := R.map (nerveMap (retract p b))
  let i := R.map (nerveMap (inclusion p b))
  let qX := R.map (pointMap X)
  let qY := R.map (pointMap Y)
  haveI : WeakEquivalence (pointMap Y) := (weakEquivalence_iff_GW _).mpr h
  haveI : WeakEquivalence qY := FiniteWeakCover.weak_singular _
  haveI : IsIso (L.map qY) := Localization.inverts L (weakEquivalences SSet.{0}) qY
    ((weakEquivalence_iff qY).mp inferInstance)
  have hr : r ≫ qY = qX := by
    rw [← Functor.map_comp]
    exact congrArg R.map (pointIsTerminal.hom_ext _ _)
  have hi : i ≫ qX = qY := by
    rw [← Functor.map_comp]
    exact congrArg R.map (pointIsTerminal.hom_ext _ _)
  have hH : SSet.Homotopy (r ≫ i) (𝟙 (R.obj X)) := by
    have h₀ : nerveMap (retract p b ⋙ inclusion p b) =
        nerveMap (retract p b) ≫ nerveMap (inclusion p b) :=
      nerveFunctor.map_comp (retract p b).toCatHom (inclusion p b).toCatHom
    have h₁ : nerveMap (𝟭 (StructuredArrow b p)) = 𝟙 X :=
      nerveFunctor.map_id (Cat.of (StructuredArrow b p))
    exact (natTransHomotopyR (deformation p b)).congr
      ((congrArg R.map h₀).trans (CategoryTheory.Functor.map_comp R _ _))
      ((congrArg R.map h₁).trans (CategoryTheory.Functor.map_id R _))
  have hL : L.map r ≫ L.map i = 𝟙 _ := by
    rw [← L.map_comp, ← L.map_id]
    exact (LeftHomotopyRel.factorsThroughLocalization (SSet.{0})
      ((DaggerStandardSSetCylinder.model_iff_literal _ _).mpr ⟨hH⟩)).map_eq L
  have hinv : L.map qX ≫ (inv (L.map qY) ≫ L.map i) = 𝟙 _ := by
    rw [← hr, L.map_comp, Category.assoc, IsIso.hom_inv_id_assoc, hL]
  have hhom : (inv (L.map qY) ≫ L.map i) ≫ L.map qX = 𝟙 _ := by
    rw [Category.assoc, ← L.map_comp, hi, IsIso.inv_hom_id]
  letI : IsIso (L.map qX) := ⟨⟨_, hinv, hhom⟩⟩
  haveI : WeakEquivalence qX :=
    (DaggerNativeAllCofibrantLocalizationSaturation.weakEquivalence_iff_localization_isIso
      L qX).mpr inferInstance
  have hn : pointMap X ≫ sSetTopAdj.unit.app _ = sSetTopAdj.unit.app X ≫ qX :=
    sSetTopAdj.unit.naturality (pointMap X)
  exact (weakEquivalence_iff_GW _).mp (weakEquivalence_of_postcomp_of_fac hn)

/-- The projection is Kan weak whenever all the original fibers are weakly contractible. -/
theorem projection_weak (h : ∀ b, GW (pointMap (nerve (Fiber p b)))) :
    WeakEquivalence (nerveMap p) :=
  (weakEquivalence_iff_GW _).mpr
    (DaggerNativeDualTheoremA.nerveMap_GW p fun b ↦ comma_point_GW p b (h b))

end
end DaggerModels.PartII.FiberedNerveCriterion
