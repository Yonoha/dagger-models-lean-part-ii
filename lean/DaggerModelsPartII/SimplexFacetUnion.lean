import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-! The facet intersections used to attach the faces of a horn one at a time. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerModels.PartII

/-- The union of the selected codimension-one faces of the standard simplex. -/
def simplexFacetUnion (n : ℕ) (S : Finset (Fin (n + 1))) : (Δ[n] : SSet.{u}).Subcomplex :=
  ⨆ i : S, SSet.stdSimplex.face {i.val}ᶜ

/-- All codimension-one faces give the boundary. -/
theorem simplexFacetUnion_univ (n : ℕ) :
    simplexFacetUnion.{u} n Finset.univ = SSet.boundary n := by
  unfold simplexFacetUnion
  rw [SSet.boundary_eq_iSup]
  apply le_antisymm
  · exact iSup_le (fun i ↦ le_iSup
      (fun j : Fin (n + 1) ↦ SSet.stdSimplex.face {j}ᶜ) i.val)
  · apply iSup_le
    intro i
    exact le_iSup (fun j : (Finset.univ : Finset (Fin (n + 1))) ↦
      SSet.stdSimplex.face {j.val}ᶜ) ⟨i, Finset.mem_univ _⟩

/-- Omitting the facet indexed by `i` gives the horn indexed by `i`. -/
theorem simplexFacetUnion_compl_singleton (n : ℕ) (i : Fin (n + 1)) :
    simplexFacetUnion.{u} n {i}ᶜ = SSet.horn n i := by
  unfold simplexFacetUnion
  rw [SSet.horn_eq_iSup]
  apply le_antisymm
  · apply iSup_le
    intro j
    exact le_iSup (fun k : ({i}ᶜ : Set (Fin (n + 1))) ↦
      SSet.stdSimplex.face {k.val}ᶜ) ⟨j.val, by
        simpa only [Finset.mem_compl, Finset.mem_singleton, Set.mem_compl_iff,
          Set.mem_singleton_iff] using j.property⟩
  · apply iSup_le
    intro j
    exact le_iSup (fun k : ({i}ᶜ : Finset (Fin (n + 1))) ↦
      SSet.stdSimplex.face {k.val}ᶜ) ⟨j.val, by
        simpa only [Finset.mem_compl, Finset.mem_singleton, Set.mem_compl_iff,
          Set.mem_singleton_iff] using j.property⟩

/-- Restriction of another facet to the face `δ i` removes its corresponding vertex. -/
theorem preimage_facet_succAbove {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    (SSet.stdSimplex.face.{u} {i.succAbove j}ᶜ).preimage (SSet.stdSimplex.δ i) =
      SSet.stdSimplex.face {j}ᶜ := by
  ext d x
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, op ⦋m⦌ = d :=
    ⟨d.unop.len, congrArg op (SimplexCategory.ext _ _ rfl)⟩
  change (SSet.stdSimplex.δ i).app (op ⦋m⦌) x ∈
    (SSet.stdSimplex.face {i.succAbove j}ᶜ).obj _ ↔
      x ∈ (SSet.stdSimplex.face {j}ᶜ).obj _
  rw [SSet.stdSimplex.mem_face_iff, SSet.stdSimplex.mem_face_iff]
  change (∀ k, i.succAbove (x k) ∈ ({i.succAbove j}ᶜ : Finset _)) ↔
    ∀ k, x k ∈ ({j}ᶜ : Finset _)
  simp only [Finset.mem_compl, Finset.mem_singleton, Fin.succAbove_right_injective.eq_iff]

/-- Restricting a union of other facets to a new facet is the corresponding smaller union. -/
theorem preimage_simplexFacetUnion_succAbove {n : ℕ} (i : Fin (n + 2))
    (S : Finset (Fin (n + 1))) :
    (simplexFacetUnion.{u} (n + 1) (S.image i.succAbove)).preimage (SSet.stdSimplex.δ i) =
      simplexFacetUnion n S := by
  unfold simplexFacetUnion
  rw [SSet.Subcomplex.preimage_iSup]
  apply le_antisymm
  · apply iSup_le
    intro j
    obtain ⟨k, hk, hkj⟩ := Finset.mem_image.mp j.property
    change (SSet.stdSimplex.face {j.val}ᶜ).preimage _ ≤ _
    rw [← hkj, preimage_facet_succAbove]
    exact le_iSup (fun j : S ↦ SSet.stdSimplex.face {j.val}ᶜ) ⟨k, hk⟩
  · apply iSup_le
    intro k
    rw [← preimage_facet_succAbove i k.val]
    exact le_iSup (fun j : S.image i.succAbove ↦
      (SSet.stdSimplex.face {j.val}ᶜ).preimage (SSet.stdSimplex.δ i))
      ⟨i.succAbove k.val, Finset.mem_image_of_mem _ k.property⟩

/-- Inserting a facet adjoins its subcomplex by a union. -/
theorem simplexFacetUnion_insert {n : ℕ} (S : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    simplexFacetUnion.{u} n (insert i S) = simplexFacetUnion n S ⊔
      SSet.stdSimplex.face {i}ᶜ := by
  unfold simplexFacetUnion
  apply le_antisymm
  · apply iSup_le
    intro j
    rcases Finset.mem_insert.mp j.property with h | h
    · rw [h]
      exact le_sup_right
    · exact le_trans
        (le_iSup (fun k : S ↦ SSet.stdSimplex.face {k.val}ᶜ) ⟨j.val, h⟩) le_sup_left
  · apply sup_le
    · apply iSup_le
      intro j
      exact le_iSup (fun k : (insert i S : Finset (Fin (n + 1))) ↦ SSet.stdSimplex.face {k.val}ᶜ)
        ⟨j.val, Finset.mem_insert_of_mem j.property⟩
    · exact le_iSup (fun k : (insert i S : Finset (Fin (n + 1))) ↦ SSet.stdSimplex.face {k.val}ᶜ)
        ⟨i, Finset.mem_insert_self _ _⟩

/-- The intersection for attaching a new facet is the smaller facet union inside it. -/
theorem simplexFacetUnion_inter_facet {n : ℕ} (i : Fin (n + 2))
    (S : Finset (Fin (n + 1))) :
    simplexFacetUnion.{u} (n + 1) (S.image i.succAbove) ⊓ SSet.stdSimplex.face {i}ᶜ =
      (simplexFacetUnion n S).image (SSet.stdSimplex.δ i) := by
  rw [← preimage_simplexFacetUnion_succAbove i S, ← SSet.stdSimplex.range_δ]
  ext d x
  exact (Set.ext_iff.mp Set.image_preimage_eq_inter_range x).symm

/-- The facet union after an insertion is the pushout of the old union and the new facet
along the image of the smaller facet union. -/
theorem simplexFacetUnion_attach {n : ℕ} (i : Fin (n + 2))
    (S : Finset (Fin (n + 1))) :
    SSet.Subcomplex.BicartSq ((simplexFacetUnion.{u} n S).image (SSet.stdSimplex.δ i))
      (simplexFacetUnion (n + 1) (S.image i.succAbove))
      (SSet.stdSimplex.face {i}ᶜ)
      (simplexFacetUnion (n + 1) (insert i (S.image i.succAbove))) where
  sup_eq := (simplexFacetUnion_insert _ _).symm
  inf_eq := simplexFacetUnion_inter_facet i S

end DaggerModels.PartII
