import DaggerModelsPartII.ReedyBoundary

/-!
# Image factorization in the opposite simplex category

An arrow of `Δᵒᵖ` first goes through an opposite face and then through an
opposite surjection. The intermediate degree is bounded by both endpoint
degrees. The comparison with any other such factorization is the unique
transport between the equal simplex objects.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII

noncomputable section

variable {s t : SimplexCategoryᵒᵖ}

/-- The intermediate object of the Reedy factorization. -/
def simplexReedyMid (f : s ⟶ t) : SimplexCategoryᵒᵖ :=
  op (image f.unop)

/-- The degree-lowering part, opposite to an injection. -/
def simplexReedyInverse (f : s ⟶ t) : s ⟶ simplexReedyMid f :=
  (image.ι f.unop).op

/-- The degree-raising part, opposite to a surjection. -/
def simplexReedyDirect (f : s ⟶ t) : simplexReedyMid f ⟶ t :=
  (factorThruImage f.unop).op

instance simplexReedyInverse_mono (f : s ⟶ t) :
    Mono (simplexReedyInverse f).unop :=
  inferInstanceAs (Mono (image.ι f.unop))

instance simplexReedyDirect_epi (f : s ⟶ t) :
    Epi (simplexReedyDirect f).unop :=
  inferInstanceAs (Epi (factorThruImage f.unop))

@[simp] theorem simplexReedyFactor_fac (f : s ⟶ t) :
    simplexReedyInverse f ≫ simplexReedyDirect f = f :=
  Quiver.Hom.unop_inj (image.fac f.unop)

theorem simplexReedyMid_le_source (f : s ⟶ t) :
    (simplexReedyMid f).unop.len ≤ s.unop.len :=
  SimplexCategory.len_le_of_mono (image.ι f.unop)

theorem simplexReedyMid_le_target (f : s ⟶ t) :
    (simplexReedyMid f).unop.len ≤ t.unop.len :=
  SimplexCategory.len_le_of_epi (factorThruImage f.unop)

/-- A nonidentity endomorphism of a simplex factors through a smaller degree. -/
theorem simplexReedyMid_lt_of_ne_id (f : s ⟶ s) (hf : f ≠ 𝟙 s) :
    (simplexReedyMid f).unop.len < s.unop.len := by
  refine lt_of_le_of_ne (simplexReedyMid_le_source f) (fun h ↦ hf ?_)
  letI : IsIso (image.ι f.unop) := (SimplexCategory.isIso_iff_of_mono _).mpr h
  letI : IsIso (factorThruImage f.unop) :=
    (SimplexCategory.isIso_iff_of_epi _).mpr h.symm
  haveI : IsIso f.unop := by
    rw [← image.fac f.unop]
    infer_instance
  exact Quiver.Hom.unop_inj (SimplexCategory.eq_id_of_isIso f.unop)

theorem simplexReedyMid_eq_of_factor {m : SimplexCategoryᵒᵖ}
    {f : s ⟶ t} {l : s ⟶ m} {r : m ⟶ t} [Mono l.unop] [Epi r.unop]
    (fac : l ≫ r = f) : simplexReedyMid f = m :=
  congrArg op (SimplexCategory.image_eq (congrArg Quiver.Hom.unop fac))

/-- In the opposite simplex category an isomorphism between equal objects is the transport. -/
theorem simplexOp_iso_eqToHom {a b : SimplexCategoryᵒᵖ} (g : a ⟶ b) [IsIso g]
    (h : a = b) : g = eqToHom h := by
  subst b
  apply Quiver.Hom.unop_inj
  exact SimplexCategory.eq_id_of_isIso g.unop

/-- Compare the two components with an arbitrary opposite-face/opposite-surjection factorization. -/
theorem simplexReedyFactor_compare {m : SimplexCategoryᵒᵖ}
    {f : s ⟶ t} {l : s ⟶ m} {r : m ⟶ t} [Mono l.unop] [Epi r.unop]
    (fac : l ≫ r = f) :
    simplexReedyInverse f ≫ eqToHom (simplexReedyMid_eq_of_factor fac) = l ∧
      eqToHom (simplexReedyMid_eq_of_factor fac) ≫ r = simplexReedyDirect f := by
  haveI : StrongEpi r.unop := strongEpi_of_epi r.unop
  have h : r.unop ≫ l.unop = f.unop := congrArg Quiver.Hom.unop fac
  let e := image.isoStrongEpiMono r.unop l.unop h
  have he : e.op.hom = eqToHom (simplexReedyMid_eq_of_factor fac) :=
    simplexOp_iso_eqToHom _ _
  rw [← he]
  constructor
  · apply Quiver.Hom.unop_inj
    exact image.isoStrongEpiMono_hom_comp_ι r.unop l.unop h
  · apply Quiver.Hom.unop_inj
    change r.unop ≫ e.hom = factorThruImage f.unop
    rw [← cancel_mono (image.ι f.unop), Category.assoc,
      image.isoStrongEpiMono_hom_comp_ι, image.fac, h]

end

end DaggerModels.PartII
