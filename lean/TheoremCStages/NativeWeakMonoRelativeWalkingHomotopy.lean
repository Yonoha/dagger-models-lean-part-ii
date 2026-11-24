import NativeKanTrivialFibrationRelativeWalkingPath
import NativeWeakMonoWholeRestriction
import NativeConstantIhomMaps

/-!
# An exact relative walking homotopy for an original Joyal-weak monomorphism

The actual internal-Hom restriction of a Joyal-weak monomorphism into a
quasicategory is a Kan trivial fibration. Its strict fiber supplies a
walking-isomorphism homotopy between maps that agree on the domain, and
uncurrying keeps the homotopy exactly fixed there.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open CartesianMonoidalCategory HomotopicalAlgebra
open DaggerActualFreeWalkingIsoIntegerObstruction
open DaggerActualFreeAntiWalkingCategoricalCylinder
open DaggerNativeIhomHoObjects DaggerNativeConstantIhomMaps
open DaggerNativeWeakMonoWholeRestriction
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.NativeWeakMonoRelativeWalkingHomotopy

noncomputable section

private theorem const_curry {A B : SSet.{u}} (K : SSet.{u}) (f : A ⟶ B) :
    (SSet.const (SSet.hoFunctor.obj.equiv _ (homObject f)) :
      K ⟶ (ihom A).obj B) = constantHom K f := by
  let x := SSet.hoFunctor.obj.equiv ((ihom A).obj B) (homObject f)
  have hc : (SSet.const x : 𝟙_ SSet.{u} ⟶ (ihom A).obj B) =
      MonoidalClosed.curry' f := by
    apply (SSet.unitHomEquiv _).injective
    change x = (SSet.unitHomEquiv _) (MonoidalClosed.curry' f)
    rfl
  calc
    (SSet.const x : K ⟶ (ihom A).obj B) =
        unitMap K ≫ (SSet.const x : 𝟙_ SSet.{u} ⟶ (ihom A).obj B) := by
          rw [SSet.comp_const]
    _ = unitMap K ≫ MonoidalClosed.curry' f := by
          rw [hc]
    _ = constantHom K f := rfl

/-- Two original maps agreeing on a Joyal-weak monomorphism are joined by a
walking-isomorphism homotopy fixed exactly on that monomorphism. -/
theorem exists_relative_homotopy {A C B : SSet.{u}} (i : A ⟶ C) [Mono i]
    (hi : DaggerNativeJoyalMappingTest.weakCategoricalEquivalences i)
    [B.Quasicategory] (f g : C ⟶ B) (h : i ≫ f = i ≫ g) :
    ∃ H : C ⊗ J.{u} ⟶ B,
      intervalEndpoint C false ≫ H = f ∧
      intervalEndpoint C true ≫ H = g ∧
      (i ▷ J.{u}) ≫ H = fst A J.{u} ≫ i ≫ f := by
  let q : (ihom C).obj B ⟶ (ihom A).obj B := (MonoidalClosed.pre i).app B
  have hq : HomotopicalAlgebra.trivialFibrations SSet.{u} q :=
    restriction_Kan_trivial i hi B
  let x : ((ihom C).obj B).obj (op ⦋0⦌) :=
    SSet.hoFunctor.obj.equiv _ (homObject f)
  let y : ((ihom C).obj B).obj (op ⦋0⦌) :=
    SSet.hoFunctor.obj.equiv _ (homObject g)
  have hx : q.app (op ⦋0⦌) x =
      SSet.hoFunctor.obj.equiv _ (homObject (i ≫ f)) := by
    change (MonoidalClosed.curry' f ≫ q).app (op ⦋0⦌) PUnit.unit =
      (MonoidalClosed.curry' (i ≫ f)).app (op ⦋0⦌) PUnit.unit
    rw [curry'_pre]
  have hy : q.app (op ⦋0⦌) y =
      SSet.hoFunctor.obj.equiv _ (homObject (i ≫ g)) := by
    change (MonoidalClosed.curry' g ≫ q).app (op ⦋0⦌) PUnit.unit =
      (MonoidalClosed.curry' (i ≫ g)).app (op ⦋0⦌) PUnit.unit
    rw [curry'_pre]
  have hxy : q.app (op ⦋0⦌) x = q.app (op ⦋0⦌) y := by
    rw [hx, hy, h]
  obtain ⟨Hbar, hzero, hone, himage⟩ :=
    NativeKanTrivialFibrationRelativeWalkingPath.exists_relative_walking_path
      q hq x y hxy
  have hzero' : DaggerNativeHoIsoWholeWalkingHomotopy.parameterPoint false ≫ Hbar =
      MonoidalClosed.curry' f := by
    exact DaggerNativeHoIsoWholeWalkingHomotopy.point_comp_eq_curry
      f Hbar false zeroInclusion rfl hzero
  have hone' : DaggerNativeHoIsoWholeWalkingHomotopy.parameterPoint true ≫ Hbar =
      MonoidalClosed.curry' g := by
    exact DaggerNativeHoIsoWholeWalkingHomotopy.point_comp_eq_curry
      g Hbar true DaggerNativeHoIsoWalkingExtension.oneInclusion rfl hone
  have himage' : Hbar ≫ q = constantHom J.{u} (i ≫ f) := by
    calc
      Hbar ≫ q = SSet.const (q.app (op ⦋0⦌) x) := himage
      _ = SSet.const (SSet.hoFunctor.obj.equiv _ (homObject (i ≫ f))) := by
        rw [hx]
      _ = constantHom J.{u} (i ≫ f) := const_curry J.{u} (i ≫ f)
  refine ⟨MonoidalClosed.uncurry Hbar,
    DaggerNativeHoIsoWholeWalkingHomotopy.uncurry_endpoint f Hbar false hzero',
    DaggerNativeHoIsoWholeWalkingHomotopy.uncurry_endpoint g Hbar true hone', ?_⟩
  rw [← MonoidalClosed.uncurry_pre_app, himage', uncurry_constant]

#print axioms exists_relative_homotopy

end

end DaggerModels.PartII.NativeWeakMonoRelativeWalkingHomotopy
