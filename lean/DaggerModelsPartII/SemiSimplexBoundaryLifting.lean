import TopCatModelCategory.SemiSimplexCategory
import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-!
# Compatible proper-face lifting for a semisimplicial map

The target is the restriction of an actual simplicial set, so its simplex
operators remain the original ones. Source operators are injective faces.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.SemiSimplexBoundaryLifting

noncomputable section

private abbrev inclusion := SemiSimplexCategory.toSimplexCategory
private abbrev restriction (X : SSet.{0}) := inclusion.op ⋙ X

/-- Every proper face remains proper after a further injective restriction. -/
private theorem proper_comp {l m n : SemiSimplexCategory}
    (a : l ⟶ m) (h : m.len < n.len) : l.len < n.len :=
  (SimplexCategory.len_le_of_mono (inclusion.map a)).trans_lt h

/-- A full compatible boundary in the semisimplicial source. The field
contains all proper injective operators, rather than only codimension-one
faces, so compatibility is stated without a choice of face decomposition. -/
structure Boundary (E : SemiSimplexCategoryᵒᵖ ⥤ Type) (n : SemiSimplexCategory) where
  face : ∀ {m : SemiSimplexCategory} (_j : m ⟶ n)
    (_h : m.len < n.len), E.obj (op m)
  naturality : ∀ {l m : SemiSimplexCategory} (a : l ⟶ m)
    (j : m ⟶ n) (h : m.len < n.len),
      face (a ≫ j) (proper_comp a h) = E.map a.op (face j h)

/-- Every prescribed source face maps to the exact corresponding face of
the unchanged target simplex. -/
def Boundary.Over {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {n : SemiSimplexCategory} {X : SSet.{0}} (α : E ⟶ restriction X)
    (b : Boundary E n) (y : X.obj (op (inclusion.obj n))) : Prop :=
  ∀ {m : SemiSimplexCategory} (j : m ⟶ n) (h : m.len < n.len),
    α.app (op m) (b.face j h) =
      X.map (inclusion.map j).op y

/-- The exact relative lifting input: a compatible full boundary and its
target equations extend to a simplex with all face equations preserved. -/
def HasBoundaryLifting {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} (α : E ⟶ restriction X) : Prop :=
  ∀ (n : SemiSimplexCategory) (y : X.obj (op (inclusion.obj n)))
    (b : Boundary E n), b.Over α y →
      ∃ e : E.obj (op n),
        α.app (op n) e = y ∧
          ∀ {m : SemiSimplexCategory} (j : m ⟶ n) (h : m.len < n.len),
            E.map j.op e = b.face j h

/-- Boundary lifting is invariant under an exact isomorphism of source
presheaves. The filler is sent back along the inverse isomorphism. -/
theorem HasBoundaryLifting.precompIso {E F : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : F ⟶ restriction X} (hα : HasBoundaryLifting α) (e : E ≅ F) :
    HasBoundaryLifting (e.hom ≫ α) := by
  intro n y B hB
  let B' : Boundary F n :=
    { face := fun j h ↦ e.hom.app _ (B.face j h)
      naturality := fun a j h ↦ by
        rw [B.naturality]
        exact congrFun (e.hom.naturality a.op) (B.face j h) }
  have hB' : B'.Over α y := hB
  obtain ⟨z, hz, zFaces⟩ := hα n y B' hB'
  refine ⟨e.inv.app _ z, ?_, ?_⟩
  · change α.app _ (e.hom.app _ (e.inv.app (op n) z)) = y
    have he : e.hom.app _ (e.inv.app (op n) z) = z :=
      congrFun (NatTrans.congr_app e.inv_hom_id (op n)) z
    rw [he, hz]
  · intro m j h
    have he : e.inv.app (op m) (F.map j.op z) = E.map j.op (e.inv.app (op n) z) :=
      congrFun (e.inv.naturality j.op) z
    rw [← he, zFaces j h]
    exact congrFun (NatTrans.congr_app e.hom_inv_id (op m)) (B.face j h)

end
end DaggerModels.PartII.SemiSimplexBoundaryLifting
