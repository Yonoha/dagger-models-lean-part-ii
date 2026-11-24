import DaggerModelsPartII.KanLeftProper
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-!
# The actual union of a monomorphism's range and a subcomplex
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.JTSubcomplexRangeUnion

open SSet.Subcomplex

noncomputable section

variable {X Y : SSet.{u}} (f : X ⟶ Y) (A : Y.Subcomplex)

private theorem preimage_image_eq :
    (A.preimage f).image f = range f ⊓ A := by
  ext n y
  change (∃ x, f.app n x ∈ A.obj n ∧ f.app n x = y) ↔
    (∃ x, f.app n x = y) ∧ y ∈ A.obj n
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, hx⟩
  · rintro ⟨⟨x, rfl⟩, hx⟩
    exact ⟨x, hx, rfl⟩

private def overlap [Mono f] :
    (A.preimage f : SSet.{u}) ≅ ((range f ⊓ A : Y.Subcomplex) : SSet.{u}) := by
  haveI : Mono ((A.preimage f).toImage f) := mono_of_mono_fac (toImage_ι _ _)
  haveI : IsIso ((A.preimage f).toImage f) := isIso_of_mono_of_epi _
  exact asIso ((A.preimage f).toImage f) ≪≫
    SSet.Subcomplex.toSSetFunctor.mapIso (eqToIso (preimage_image_eq f A))

private theorem map_eqToHom_ι {B C : Y.Subcomplex} (h : B = C) :
    SSet.Subcomplex.toSSetFunctor.map (eqToHom h) ≫ C.ι = B.ι := by
  subst C
  simp

private theorem overlap_ι [Mono f] :
    (overlap f A).hom ≫ (range f ⊓ A : Y.Subcomplex).ι = (A.preimage f).ι ≫ f := by
  simp only [overlap, Iso.trans_hom, Category.assoc, Functor.mapIso_hom, eqToIso.hom,
    map_eqToHom_ι, asIso_hom, toImage_ι]

/-- The union as a subcomplex of the actual codomain. -/
abbrev union : Y.Subcomplex := range f ⊔ A

/-- The original domain maps into the union through its actual range. -/
def inl : X ⟶ (union f A : SSet.{u}) :=
  toRange f ≫ SSet.Subcomplex.homOfLE le_sup_left

/-- The given subcomplex includes into the union. -/
def inr : (A : SSet.{u}) ⟶ (union f A : SSet.{u}) :=
  SSet.Subcomplex.homOfLE le_sup_right

@[reassoc (attr := simp)]
theorem inl_ι : inl f A ≫ (union f A).ι = f := by
  simp [inl]

@[reassoc (attr := simp)]
theorem inr_ι : inr f A ≫ (union f A).ι = A.ι :=
  rfl

/-- The union is the pushout of the actual preimage and the original domain. -/
theorem isPushout [Mono f] :
    IsPushout (A.preimage f).ι (A.fromPreimage f) (inl f A) (inr f A) := by
  let s : BicartSq (range f ⊓ A) (range f) A (union f A) := ⟨rfl, rfl⟩
  refine s.isPushout.of_iso' (overlap f A) (asIso (toRange f)) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · rw [← cancel_mono (range f).ι]
    simp only [Category.assoc, homOfLE_ι, overlap_ι, asIso_hom, toRange_ι]
  · rw [← cancel_mono A.ι]
    simp only [Category.assoc, homOfLE_ι, overlap_ι, Iso.refl_hom, Category.comp_id,
      fromPreimage_ι]
  · simp only [inl, asIso_hom, Iso.refl_hom, Category.comp_id]
  · simp only [inr, Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- A weak preimage comparison over a mono weak equivalence gives a weak
inclusion of the whole union. -/
theorem union_weak [Mono f] [WeakEquivalence f]
    (hA : WeakEquivalence (A.fromPreimage f)) :
    WeakEquivalence (union f A).ι := by
  haveI : WeakEquivalence (inl f A) := (weakEquivalence_iff _).mpr
    (kanLeftProper (isPushout f A)
      ((cofibration_iff _).mp (SSet.modelCategoryQuillen.cofibration_of_mono _))
      ((weakEquivalence_iff _).mp hA))
  exact weakEquivalence_of_precomp_of_fac (inl_ι f A)

end

end DaggerModels.PartII.JTSubcomplexRangeUnion
