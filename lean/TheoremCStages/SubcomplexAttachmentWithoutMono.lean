import NativeSubcomplexAttachmentPushout

/-!
# Attach a simplex map which is injective only away from the old subcomplex

The existing native attachment proof uses a monomorphic simplex map. The
pinned type-level pushout criterion only requires injectivity on the complement
of the attaching subcomplex. Applying that criterion degreewise removes the
unnecessary global monomorphism hypothesis while retaining the actual
preimage, inclusions, generated subcomplex, and pushout square.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Simplicial Opposite

universe u

namespace DaggerModels.PartII.SubcomplexAttachmentWithoutMono

noncomputable section

/-- An actual map may repeat old simplices; injectivity is required only
on the simplices outside its exact preimage of the existing subcomplex. -/
theorem attachment_isPushout {X K : SSet.{u}} (H D : X.Subcomplex) (b : K ⟶ X)
    (hH : H ≤ D) (hb : SSet.Subcomplex.range b ≤ D)
    (hcover : H ⊔ SSet.Subcomplex.range b = D)
    (hinject : ∀ (q : SimplexCategoryᵒᵖ) (x y : K.obj q),
      x ∉ (H.preimage b).obj q → y ∉ (H.preimage b).obj q →
        b.app q x = b.app q y → x = y) :
    IsPushout (H.fromPreimage b) (H.preimage b).ι
      (SSet.Subcomplex.homOfLE hH) (SSet.Subcomplex.lift b hb) := by
  apply IsPushout.of_isColimit
    (c := PushoutCocone.mk (SSet.Subcomplex.homOfLE hH)
      (SSet.Subcomplex.lift b hb) (by rfl))
  apply evaluationJointlyReflectsColimits _
  intro q
  apply (PushoutCocone.isColimitMapCoconeEquiv _ _).2
  apply IsPushout.isColimit
  dsimp
  refine Types.isPushout_of_isPullback_of_mono (X₅ := X.obj q) (k := Subtype.val)
    (r' := Subtype.val) (b' := b.app q) ?_ rfl rfl ?_ ?_
  · exact Types.isPullback_of_eq_setPreimage (b.app q) (H.obj q) rfl
  · apply Set.eq_univ_of_forall
    rintro ⟨x, hx⟩
    have hc : x ∈ (H ⊔ SSet.Subcomplex.range b).obj q := by
      rw [hcover]
      exact hx
    rcases hc with hh | ⟨y, hy⟩
    · exact Or.inl ⟨⟨x, hh⟩, rfl⟩
    · exact Or.inr ⟨y, Subtype.ext hy⟩
  · intro x y hx hy hxy
    apply hinject q x y
    · intro h
      exact hx ⟨⟨x, h⟩, rfl⟩
    · intro h
      exact hy ⟨⟨y, h⟩, rfl⟩
    · exact hxy

#print axioms attachment_isPushout

end

end DaggerModels.PartII.SubcomplexAttachmentWithoutMono
