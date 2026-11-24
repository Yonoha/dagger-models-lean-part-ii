import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# A section presentation of a pushout

A second pushout combines the old attaching source with an object mapping
into the old target. If its projection restricts to the attaching projection
and to the identity, the old pushout is also the pushout of that combined map.
-/

set_option autoImplicit false

universe v u

open CategoryTheory Limits

namespace DaggerModels.PartII.PushoutSectionTensor

/-- Re-present a pushout using a second pushout and a section of its projection.
All four displayed maps are retained in the resulting pushout square. -/
theorem isPushout {C : Type u} [Category.{v} C]
    {A B D E P Q S : C}
    {u : A ⟶ B} {a : A ⟶ D} {b : B ⟶ Q} {j : D ⟶ Q}
    {f : S ⟶ A} {g : S ⟶ E} {l : A ⟶ P} {t : E ⟶ P}
    (h : IsPushout u a b j) (hP : IsPushout f g l t)
    (q : P ⟶ B) (p : P ⟶ E) (r : E ⟶ B) (c : D ⟶ E)
    (hlq : l ≫ q = u) (htq : t ≫ q = r)
    (hlp : l ≫ p = a ≫ c) (htp : t ≫ p = 𝟙 E)
    (hc : c ≫ r ≫ b = j) : IsPushout q p b (r ≫ b) := by
  have hw : q ≫ b = p ≫ (r ≫ b) := by
    apply hP.hom_ext
    · rw [← Category.assoc, hlq, ← Category.assoc, hlp]
      rw [Category.assoc, hc]
      exact h.w
    · rw [← Category.assoc, htq, ← Category.assoc, htp, Category.id_comp]
  let descend (z : PushoutCocone q p) : Q ⟶ z.pt :=
    h.desc z.inl (c ≫ z.inr) (by
      have hz := congrArg (fun k ↦ l ≫ k) z.condition
      dsimp only at hz
      simp only [← Category.assoc] at hz
      rw [hlq, hlp] at hz
      simpa only [Category.assoc] using hz)
  apply IsPushout.of_isColimit
    (c := PushoutCocone.mk b (r ≫ b) hw)
  refine PushoutCocone.IsColimit.mk hw descend ?_ ?_ ?_
  · intro z
    exact h.inl_desc _ _ _
  · intro z
    dsimp only [descend]
    rw [Category.assoc, h.inl_desc]
    have hz := congrArg (fun k ↦ t ≫ k) z.condition
    dsimp only at hz
    simp only [← Category.assoc] at hz
    rw [htq, htp, Category.id_comp] at hz
    exact hz
  · intro z m hm hn
    apply h.hom_ext
    · exact hm.trans (h.inl_desc _ _ _).symm
    · calc
        j ≫ m = (c ≫ (r ≫ b)) ≫ m := by rw [hc]
        _ = c ≫ ((r ≫ b) ≫ m) := Category.assoc _ _ _
        _ = c ≫ z.inr := by rw [hn]
        _ = j ≫ descend z := (h.inr_desc _ _ _).symm

end DaggerModels.PartII.PushoutSectionTensor
