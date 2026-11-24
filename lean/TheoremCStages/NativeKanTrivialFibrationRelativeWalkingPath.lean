import NativeHoIsoWalkingExtension
import TopCatModelCategory.SSet.FundamentalGroupoid

/-!
# A relative walking-isomorphism path over a Kan trivial fibration

The two prescribed vertices are joined by a map from the original walking
isomorphism while their common image remains exactly constant. This is the
relative path needed to correct a weak-monomorphism extension in the Joyal
isofibration argument.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open DaggerActualFreeWalkingIsoIntegerObstruction
open DaggerNativeWalkingEdgeKanInclusion DaggerNativeHoIsoWalkingExtension
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.NativeKanTrivialFibrationRelativeWalkingPath

noncomputable section

private theorem point_comp {E B : SSet.{u}} (p : E ⟶ B)
    (x : E.obj (op ⦋0⦌)) :
    SSet.yonedaEquiv.symm x ≫ p =
      (SSet.const (p.app (op ⦋0⦌) x) : (Δ[0] : SSet.{u}) ⟶ B) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  exact (SSet.yonedaEquiv_const _).symm

/-- A Kan trivial fibration connects two vertices in the same strict fiber
by the original walking isomorphism, with exact endpoints and constant image. -/
theorem exists_relative_walking_path {E B : SSet.{u}} (p : E ⟶ B)
    (hp : trivialFibrations SSet.{u} p)
    (x y : E.obj (op ⦋0⦌))
    (hxy : p.app (op ⦋0⦌) x = p.app (op ⦋0⦌) y) :
    ∃ H : J.{u} ⟶ E,
      zeroInclusion.{u} ≫ H = SSet.yonedaEquiv.symm x ∧
      oneInclusion.{u} ≫ H = SSet.yonedaEquiv.symm y ∧
      H ≫ p = SSet.const (p.app (op ⦋0⦌) x) := by
  let j : (SSet.boundary 1 : SSet.{u}) ⟶ J.{u} :=
    (SSet.boundary 1).ι ≫ edgeInclusion.{u}
  haveI : Mono edgeInclusion.{u} := edgeInclusion_mono
  have hjmono : Mono j := inferInstance
  have hjcof : cofibrations SSet.{u} j := by
    rw [SSet.modelCategoryQuillen.cofibrations_eq]
    exact monomorphisms.infer_property j
  have hr : (cofibrations SSet.{u}).rlp p := by
    rw [cofibrations_rlp]
    exact hp
  let top : (SSet.boundary 1 : SSet.{u}) ⟶ E := SSet.boundary₁.desc x y
  let bottom : J.{u} ⟶ B := SSet.const (p.app (op ⦋0⦌) x)
  have hsq : top ≫ p = j ≫ bottom := by
    simp only [bottom, SSet.comp_const]
    apply SSet.boundary₁.hom_ext
    · rw [← Category.assoc, SSet.boundary₁.ι₀_desc]
      exact point_comp p x
    · rw [← Category.assoc, SSet.boundary₁.ι₁_desc]
      rw [point_comp p y, ← hxy]
      simp only [SSet.comp_const]
  letI : HasLiftingProperty j p := hr j hjcof
  let sq : CommSq top j p bottom := ⟨hsq⟩
  let H : J.{u} ⟶ E := sq.lift
  have hzero : SSet.boundary₁.ι₀ ≫ j = zeroInclusion.{u} := by
    dsimp only [j]
    rw [← Category.assoc, SSet.boundary₁.ι₀_ι, zero_edgeInclusion]
  have hone : SSet.boundary₁.ι₁ ≫ j = oneInclusion.{u} := by
    dsimp only [j]
    rw [← Category.assoc, SSet.boundary₁.ι₁_ι, one_edgeInclusion]
  refine ⟨H, ?_, ?_, sq.fac_right⟩
  · calc
      zeroInclusion.{u} ≫ H = (SSet.boundary₁.ι₀ ≫ j) ≫ H := by rw [hzero]
      _ = SSet.boundary₁.ι₀ ≫ top := by rw [Category.assoc, sq.fac_left]
      _ = SSet.yonedaEquiv.symm x := SSet.boundary₁.ι₀_desc x y
  · calc
      oneInclusion.{u} ≫ H = (SSet.boundary₁.ι₁ ≫ j) ≫ H := by rw [hone]
      _ = SSet.boundary₁.ι₁ ≫ top := by rw [Category.assoc, sq.fac_left]
      _ = SSet.yonedaEquiv.symm y := SSet.boundary₁.ι₁_desc x y

#print axioms exists_relative_walking_path

end

end DaggerModels.PartII.NativeKanTrivialFibrationRelativeWalkingPath
