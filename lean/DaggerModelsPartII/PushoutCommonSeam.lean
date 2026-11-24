import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# A common-seam pushout pasting lemma

Four pushout squares describe two copies attached along a common seam,
followed by a collapse of that seam. Their outer comparison is again a
pushout. This is a purely categorical lemma, independent of the JT frames.
-/

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace DaggerModels.PartII.PushoutCommonSeam

/-- If a two-copy pushout is subsequently collapsed along its common seam,
the result is the pushout of the two separately collapsed copies over the
new seam. -/
theorem isPushout
    {C : Type u} [Category.{v} C]
    {S A B V D E F R : C}
    {sA : S ⟶ A} {sB : S ⟶ B} {sV : S ⟶ V}
    {aD : A ⟶ D} {bD : B ⟶ D}
    {aE : A ⟶ E} {vE : V ⟶ E}
    {bF : B ⟶ F} {vF : V ⟶ F}
    {dR : D ⟶ R} {vR : V ⟶ R}
    {eR : E ⟶ R} {fR : F ⟶ R}
    (hD : IsPushout sA sB aD bD)
    (hE : IsPushout sA sV aE vE)
    (hF : IsPushout sB sV bF vF)
    (hR : IsPushout (sA ≫ aD) sV dR vR)
    (ha : aE ≫ eR = aD ≫ dR)
    (hb : bF ≫ fR = bD ≫ dR)
    (hvE : vE ≫ eR = vR)
    (hvF : vF ≫ fR = vR) :
    IsPushout vE vF eR fR := by
  have hw : vE ≫ eR = vF ≫ fR := hvE.trans hvF.symm
  let descend (t : PushoutCocone vE vF) : R ⟶ t.pt :=
    let d : D ⟶ t.pt := hD.desc (aE ≫ t.inl) (bF ≫ t.inr) (by
      calc
        sA ≫ (aE ≫ t.inl) = (sA ≫ aE) ≫ t.inl := by rw [Category.assoc]
        _ = (sV ≫ vE) ≫ t.inl := by rw [hE.w]
        _ = sV ≫ (vE ≫ t.inl) := by rw [Category.assoc]
        _ = sV ≫ (vF ≫ t.inr) := by rw [t.condition]
        _ = (sV ≫ vF) ≫ t.inr := by rw [Category.assoc]
        _ = (sB ≫ bF) ≫ t.inr := by rw [hF.w]
        _ = sB ≫ (bF ≫ t.inr) := by rw [Category.assoc])
    hR.desc d (vE ≫ t.inl) (by
      calc
        (sA ≫ aD) ≫ d = sA ≫ (aD ≫ d) := by rw [Category.assoc]
        _ = sA ≫ (aE ≫ t.inl) := by rw [hD.inl_desc]
        _ = (sA ≫ aE) ≫ t.inl := by rw [Category.assoc]
        _ = (sV ≫ vE) ≫ t.inl := by rw [hE.w]
        _ = sV ≫ (vE ≫ t.inl) := by rw [Category.assoc])
  apply IsPushout.of_isColimit
    (c := PushoutCocone.mk eR fR hw)
  refine PushoutCocone.IsColimit.mk hw descend ?_ ?_ ?_
  · intro t
    apply hE.hom_ext
    · rw [← Category.assoc, ha, Category.assoc]
      simp only [descend, hR.inl_desc, hD.inl_desc]
    · rw [← Category.assoc, hvE]
      simp only [descend, hR.inr_desc]
  · intro t
    apply hF.hom_ext
    · rw [← Category.assoc, hb, Category.assoc]
      simp only [descend, hR.inl_desc, hD.inr_desc]
    · calc
        vF ≫ (fR ≫ descend t) = (vF ≫ fR) ≫ descend t := by
          rw [Category.assoc]
        _ = vR ≫ descend t := by rw [hvF]
        _ = vE ≫ t.inl := by
          dsimp [descend]
          rw [hR.inr_desc]
        _ = vF ≫ t.inr := t.condition
  · intro t q hqE hqF
    apply hR.hom_ext
    · apply hD.hom_ext
      · rw [← Category.assoc, ← ha, Category.assoc, hqE]
        simp only [descend, hR.inl_desc, hD.inl_desc]
      · rw [← Category.assoc, ← hb, Category.assoc, hqF]
        simp only [descend, hR.inl_desc, hD.inr_desc]
    · rw [← hvE, Category.assoc, hqE]
      dsimp [descend]
      rw [hvE, hR.inr_desc]

end DaggerModels.PartII.PushoutCommonSeam
