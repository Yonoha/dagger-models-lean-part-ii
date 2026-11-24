import DaggerModelsPartII.JTInterleavedTimeBoundary
import DaggerModelsPartII.JTFixedLiftSpaceInterleavedProjection

/-!
# Relative extension of an entire normalization prism
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial MonoidalCategory
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.JTFixedLiftSpaceInterleavedRelative

open JTFixedLiftSpaceInterleaved JTFixedLiftSpaceTimeEquiv JTHigherInterleavedParameter

noncomputable section

variable {A X Y : SSet.{u}} {k : ℕ} {i : A ⟶ (Δ[k] : SSet.{u})}
variable {t : A ⟶ X} {p : X ⟶ Y} {b : (Δ[k] : SSet.{u}) ⟶ Y}
variable (sq : CommSq t i p b)

/-- Extend the prescribed map on the full product prism and the enlarged
time boundary at once, retaining the original base and stationary
equations. -/
theorem exists_extension_relative [Fibration p] (n : ℕ)
    (v : (SSet.ihomToPullbackFiber sq).obj (op ⦋n⦌))
    (g : (timeBoundary.{u} k n : SSet.{u}) ⟶ X)
    (hg : g ≫ p = (timeBoundary k n).ι ≫ SSet.stdSimplex.map (ret ⦋k⦌ ⦋n⦌) ≫ b)
    (hoverlap : (timeBoundary k n).fromPreimage (prism ⦋k⦌ ⦋n⦌) ≫ g =
      ((timeBoundary k n).preimage (prism ⦋k⦌ ⦋n⦌)).ι ≫ timeMap sq ⦋n⦌ v) :
    ∃ E : Extension sq ⦋n⦌,
      prism ⦋k⦌ ⦋n⦌ ≫ E.map = timeMap sq ⦋n⦌ v ∧
      (timeBoundary k n).ι ≫ E.map = g := by
  let f := prism.{u} ⦋k⦌ ⦋n⦌
  let F := timeBoundary.{u} k n
  let U := JTSubcomplexRangeUnion.union f F
  let a := JTSubcomplexRangeUnion.inl f F
  let c := JTSubcomplexRangeUnion.inr f F
  let P := JTSubcomplexRangeUnion.isPushout f F
  let h := P.desc (timeMap sq ⦋n⦌ v) g hoverlap.symm
  let q := SSet.stdSimplex.map (ret ⦋k⦌ ⦋n⦌) ≫ b
  have ha : a ≫ h = timeMap sq ⦋n⦌ v := P.inl_desc _ _ _
  have hc : c ≫ h = g := P.inr_desc _ _ _
  have hA : a ≫ U.ι = f := JTSubcomplexRangeUnion.inl_ι f F
  have hC : c ≫ U.ι = F.ι := JTSubcomplexRangeUnion.inr_ι f F
  have H : h ≫ p = U.ι ≫ q := by
    apply P.hom_ext
    · rw [← Category.assoc, ha, ← Category.assoc, hA, (timeMap_conditions sq ⦋n⦌ v).2]
      dsimp only [f, q]
      rw [← Category.assoc, prism_ret]
    · rw [← Category.assoc, hc, ← Category.assoc, hC]
      exact hg
  haveI := prismTimeBoundary_weak.{u} k n
  haveI : Cofibration U.ι := SSet.modelCategoryQuillen.cofibration_of_mono _
  let lifting : CommSq h U.ι p q := ⟨H⟩
  have hf : f ≫ lifting.lift = timeMap sq ⦋n⦌ v := by
    calc
      f ≫ lifting.lift = (a ≫ U.ι) ≫ lifting.lift :=
        congrArg (fun j ↦ j ≫ lifting.lift) hA.symm
      _ = _ := by rw [Category.assoc, lifting.fac_left, ha]
  have hF : F.ι ≫ lifting.lift = g := by
    calc
      F.ι ≫ lifting.lift = (c ≫ U.ι) ≫ lifting.lift :=
        congrArg (fun j ↦ j ≫ lifting.lift) hC.symm
      _ = _ := by rw [Category.assoc, lifting.fac_left, hc]
  refine ⟨⟨lifting.lift, ?_, lifting.fac_right⟩, hf, hF⟩
  change (i ▷ (Δ[n] : SSet.{u})) ≫ f ≫ lifting.lift = _
  rw [hf]
  exact (timeMap_conditions sq ⦋n⦌ v).1

end

end DaggerModels.PartII.JTFixedLiftSpaceInterleavedRelative
