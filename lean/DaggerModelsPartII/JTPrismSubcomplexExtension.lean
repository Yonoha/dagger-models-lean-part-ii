import DaggerModelsPartII.JTSubcomplexRangeUnion

/-!
# Relative extension from the full prism and a subcomplex
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.JTPrismSubcomplexExtension

open SSet.Subcomplex

noncomputable section

/-- The two compatible maps extend along the entire union when the prism
and the comparison of the subcomplex with its preimage are weak. -/
theorem exists_extension {P K X Y : SSet.{u}} (f : P ⟶ K) [Mono f] [WeakEquivalence f]
    (F : K.Subcomplex) (hw : WeakEquivalence (F.fromPreimage f))
    {p : X ⟶ Y} [Fibration p] (q : K ⟶ Y)
    (v : P ⟶ X) (G : F.toSSet ⟶ X) (hv : v ≫ p = f ≫ q) (hG : G ≫ p = F.ι ≫ q)
    (hV : (F.preimage f).ι ≫ v = F.fromPreimage f ≫ G) :
    ∃ L : K ⟶ X, f ≫ L = v ∧ F.ι ≫ L = G ∧ L ≫ p = q := by
  let U := JTSubcomplexRangeUnion.union f F
  let a := JTSubcomplexRangeUnion.inl f F
  let b := JTSubcomplexRangeUnion.inr f F
  let S := JTSubcomplexRangeUnion.isPushout f F
  let H := S.desc v G hV
  have ha : a ≫ H = v := S.inl_desc _ _ _
  have hb : b ≫ H = G := S.inr_desc _ _ _
  have haU : a ≫ U.ι = f := JTSubcomplexRangeUnion.inl_ι f F
  have hbU : b ≫ U.ι = F.ι := JTSubcomplexRangeUnion.inr_ι f F
  have Hq : H ≫ p = U.ι ≫ q := by
    apply S.hom_ext
    · rw [← Category.assoc, ha, ← Category.assoc, haU, hv]
    · rw [← Category.assoc, hb, ← Category.assoc, hbU, hG]
  haveI : WeakEquivalence U.ι := JTSubcomplexRangeUnion.union_weak f F hw
  haveI : Cofibration U.ι := SSet.modelCategoryQuillen.cofibration_of_mono _
  let L : CommSq H U.ι p q := ⟨Hq⟩
  have hf : f ≫ L.lift = v := by
    calc
      _ = (a ≫ U.ι) ≫ L.lift := congrArg (fun k ↦ k ≫ L.lift) haU.symm
      _ = _ := by rw [Category.assoc, L.fac_left, ha]
  have hF : F.ι ≫ L.lift = G := by
    calc
      _ = (b ≫ U.ι) ≫ L.lift := congrArg (fun k ↦ k ≫ L.lift) hbU.symm
      _ = _ := by rw [Category.assoc, L.fac_left, hb]
  exact ⟨L.lift, hf, hF, L.fac_right⟩

end

end DaggerModels.PartII.JTPrismSubcomplexExtension
