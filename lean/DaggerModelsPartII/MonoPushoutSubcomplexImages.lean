import TopCatModelCategory.SSet.Subcomplex

/-!
# Intersections of images in a simplicial pushout

The image-intersection identity is restricted to two subcomplexes
containing a common representative for the seam of the pushout.
No image-meet preservation for an arbitrary quotient is asserted.
-/

set_option autoImplicit false

open CategoryTheory Limits Simplicial

namespace DaggerModels.PartII.MonoPushoutSubcomplexImages

noncomputable section

variable {S X T P : SSet.{0}} {f : S ⟶ X} {g : S ⟶ T}
  {q : X ⟶ P} {b : T ⟶ P}

/-- In an actual pushout along a monomorphism, two points of the
`X` leg with the same quotient image either coincide or both come
from the seam, with equal images in the `T` leg. -/
private theorem equal_quotient_cases
    (sq : IsPushout f g q b) [Mono f]
    (n : SimplexCategoryᵒᵖ) (x y : X.obj n)
    (hxy : q.app n x = q.app n y) :
    x = y ∨ ∃ s t : S.obj n,
      x = f.app n s ∧ y = f.app n t ∧ g.app n s = g.app n t := by
  have hfn : Function.Injective (f.app n) := by
    haveI : Mono (f.app n) :=
      (NatTrans.mono_iff_mono_app f).1 (inferInstance : Mono f) n
    exact (mono_iff_injective (f := f.app n)).1 inferInstance
  have hsq := sq.map ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj n)
  change IsPushout (f.app n) (g.app n) (q.app n) (b.app n) at hsq
  exact
    (Types.pushoutCocone_inl_eq_inl_iff_of_isColimit
      hsq.isColimit hfn x y).1 hxy

/-- The fixed representative `h : T ⟶ X` makes the quotient image
of an intersection equal the intersection of quotient images.
The attaching map `g` may identify seam points. -/
theorem image_inf_eq (sq : IsPushout f g q b) [Mono f]
    (h : T ⟶ X) (hq : h ≫ q = b)
    (A C : X.Subcomplex)
    (hA : SSet.Subcomplex.range h ≤ A)
    (hC : SSet.Subcomplex.range h ≤ C) :
    (A ⊓ C).image q = A.image q ⊓ C.image q := by
  ext n z
  change (∃ x, x ∈ (A ⊓ C).obj n ∧ q.app n x = z) ↔
    (∃ x, x ∈ A.obj n ∧ q.app n x = z) ∧
      (∃ y, y ∈ C.obj n ∧ q.app n y = z)
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx.1, rfl⟩, ⟨x, hx.2, rfl⟩⟩
  · rintro ⟨⟨x, hxA, hxz⟩, ⟨y, hyC, hyz⟩⟩
    have hxy : q.app n x = q.app n y := hxz.trans hyz.symm
    rcases equal_quotient_cases sq n x y hxy with hsame | ⟨s, _t, hs, _ht, _hst⟩
    · subst y
      exact ⟨x, ⟨hxA, hyC⟩, hxz⟩
    · let z₀ : X.obj n := h.app n (g.app n s)
      have hzA : z₀ ∈ A.obj n :=
        hA n ⟨g.app n s, rfl⟩
      have hzC : z₀ ∈ C.obj n :=
        hC n ⟨g.app n s, rfl⟩
      have hseam : q.app n (f.app n s) = b.app n (g.app n s) := by
        exact congrFun (NatTrans.congr_app sq.w n) s
      have hrep : q.app n z₀ = b.app n (g.app n s) := by
        exact congrFun (NatTrans.congr_app hq n) (g.app n s)
      refine ⟨z₀, ⟨hzA, hzC⟩, ?_⟩
      calc
        q.app n z₀ = b.app n (g.app n s) := hrep
        _ = q.app n (f.app n s) := hseam.symm
        _ = q.app n x := by rw [hs]
        _ = z := hxz

end
end DaggerModels.PartII.MonoPushoutSubcomplexImages
