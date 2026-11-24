import DaggerModelsPartII.CosimplicialMappingInvariance
import NativeAllCofibrantLocalizationSaturation

/-! Weak-equivalence tests by precomposition on homotopy mapping simplicial sets. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite
open scoped SSet.modelCategoryQuillen

universe v u

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]

private def chosenMappingComparison {A B : C} (f : A ⟶ B) :
    (cosimplicialResolution A).Comparison (cosimplicialResolution B) f :=
  (cosimplicialResolution A).comparison (cosimplicialResolution B) f

/-- Maps that induce a Kan weak equivalence of the homotopy mapping simplicial sets into
the fixed target. For fibrant targets this test is independent of the choices. -/
def homotopyMappingWeakEquivalences (Z : C) : MorphismProperty C :=
  fun _ _ f ↦ weakEquivalences SSet.{v} ((chosenMappingComparison f).precomp Z)

/-- Any two resolutions and any compatible comparison can be used for the test. -/
theorem homotopyMappingWeakEquivalences_iff (Z : C) [IsFibrant Z] {A B : C}
    {f : A ⟶ B} {R : CosimplicialResolution A} {S : CosimplicialResolution B}
    (g : R.Comparison S f) :
    homotopyMappingWeakEquivalences Z f ↔ weakEquivalences SSet.{v} (g.precomp Z) :=
  (chosenMappingComparison f).precomp_weak_iff g Z

/-- Every original weak equivalence passes the test against a fibrant target. -/
theorem weakEquivalences_le_homotopyMappingWeakEquivalences (Z : C) [IsFibrant Z] :
    weakEquivalences C ≤ homotopyMappingWeakEquivalences Z :=
  fun _ _ f hf ↦ (chosenMappingComparison f).precomp_weak hf Z

private theorem homotopyMappingWeakEquivalences_comp_iff (Z : C) [IsFibrant Z]
    {A B D : C} (f : A ⟶ B) (g : B ⟶ D) :
    homotopyMappingWeakEquivalences Z (f ≫ g) ↔ weakEquivalences SSet.{v}
      ((chosenMappingComparison g).precomp Z ≫ (chosenMappingComparison f).precomp Z) := by
  rw [homotopyMappingWeakEquivalences_iff Z
    ((chosenMappingComparison f).comp (chosenMappingComparison g)),
    CosimplicialResolution.Comparison.precomp_comp]

instance (Z : C) [IsFibrant Z] :
    (homotopyMappingWeakEquivalences Z).ContainsIdentities where
  id_mem A := weakEquivalences_le_homotopyMappingWeakEquivalences Z _
    ((weakEquivalences C).id_mem A)

instance (Z : C) [IsFibrant Z] :
    (homotopyMappingWeakEquivalences Z).HasTwoOutOfThreeProperty where
  comp_mem f g hf hg :=
    (homotopyMappingWeakEquivalences_comp_iff Z f g).mpr
      ((weakEquivalences SSet.{v}).comp_mem _ _ hg hf)
  of_precomp f g hf hfg :=
    (weakEquivalences SSet.{v}).of_postcomp _ _ hf
      ((homotopyMappingWeakEquivalences_comp_iff Z f g).mp hfg)
  of_postcomp f g hg hfg :=
    (weakEquivalences SSet.{v}).of_precomp _ _ hg
      ((homotopyMappingWeakEquivalences_comp_iff Z f g).mp hfg)

/-- The contravariant homotopy mapping functor into the Kan homotopy category. -/
def homotopyMappingFunctor (Z : C) [IsFibrant Z] :
    Cᵒᵖ ⥤ (weakEquivalences SSet.{v}).Localization where
  obj A := (weakEquivalences SSet.{v}).Q.obj ((cosimplicialResolution A.unop).mappingSSet.obj Z)
  map f := (weakEquivalences SSet.{v}).Q.map ((chosenMappingComparison f.unop).precomp Z)
  map_id A := by
    let R := cosimplicialResolution A.unop
    let h : R.Comparison R (𝟙 A).unop := ⟨𝟙 _, by simp⟩
    rw [(chosenMappingComparison (𝟙 A).unop).precomp_localized_eq h Z]
    change (weakEquivalences SSet.{v}).Q.map
      (Functor.whiskerRight (𝟙 R.oppositeDiagram) (coyoneda.obj (op (op Z)))) = _
    simp
    rfl
  map_comp f g := by
    change (weakEquivalences SSet.{v}).Q.map ((chosenMappingComparison (f ≫ g).unop).precomp Z) = _
    rw [CategoryTheory.unop_comp]
    rw [(chosenMappingComparison (g.unop ≫ f.unop)).precomp_localized_eq
      ((chosenMappingComparison g.unop).comp (chosenMappingComparison f.unop)) Z]
    rw [CosimplicialResolution.Comparison.precomp_comp, CategoryTheory.Functor.map_comp]

/-- The weak-equivalence test is invertibility under the contravariant mapping functor. -/
theorem homotopyMappingWeakEquivalences_iff_isIso (Z : C) [IsFibrant Z] {A B : C}
    (f : A ⟶ B) :
    homotopyMappingWeakEquivalences Z f ↔ IsIso ((homotopyMappingFunctor Z).map f.op) :=
  (weakEquivalence_iff _).symm.trans
    (DaggerNativeAllCofibrantLocalizationSaturation.weakEquivalence_iff_localization_isIso
      (weakEquivalences SSet.{v}).Q _)

instance (Z : C) [IsFibrant Z] :
    (homotopyMappingWeakEquivalences Z).IsStableUnderRetracts where
  of_retract {X Y A B f g} r hg := by
    let F := homotopyMappingFunctor Z
    have h : (isomorphisms _).inverseImage F g.op :=
      (homotopyMappingWeakEquivalences_iff_isIso Z g).mp hg
    exact (homotopyMappingWeakEquivalences_iff_isIso Z f).mpr
      (MorphismProperty.of_retract (P := (isomorphisms _).inverseImage F) r.op h)

/-- Replacing a fibrant target by a weakly equivalent fibrant target preserves the test. -/
theorem homotopyMappingWeakEquivalences_target_iff {Z T : C} [IsFibrant Z] [IsFibrant T]
    (p : Z ⟶ T) (hp : weakEquivalences C p) {A B : C} (f : A ⟶ B) :
    homotopyMappingWeakEquivalences Z f ↔ homotopyMappingWeakEquivalences T f := by
  let g := chosenMappingComparison f
  let a := (cosimplicialResolution A).mappingSSet.map p
  let b := (cosimplicialResolution B).mappingSSet.map p
  have w : g.precomp Z ≫ a = b ≫ g.precomp T := by
    ext n x : 2
    change op Z ⟶ (cosimplicialResolution B).oppositeDiagram.obj n at x
    apply Quiver.Hom.unop_inj
    exact Category.assoc (g.mapOp.app n).unop x.unop p
  have ha := (cosimplicialResolution A).mappingSSet_map_weak p hp
  have hb := (cosimplicialResolution B).mappingSSet_map_weak p hp
  constructor
  · intro h
    exact (weakEquivalences SSet.{v}).of_precomp _ _ hb
      (w ▸ (weakEquivalences SSet.{v}).comp_mem _ _ h ha)
  · intro h
    exact (weakEquivalences SSet.{v}).of_postcomp _ _ ha
      (w.symm ▸ (weakEquivalences SSet.{v}).comp_mem _ _ hb h)

end

end DaggerModels.PartII
