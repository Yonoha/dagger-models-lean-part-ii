import NativeSimplicialReplacementCells
import NativeOverNerveSimplexFamily

/-!
# A set-valued local system over the nerve of a category

A simplex is a chain in the category together with a value at its
initial object. Restriction transports that value along the chain's
initial arrow. No groupoid structure on the base category is required.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial
open DaggerNativeSimplicialReplacementCells (first initialArrow initialArrow_id initialArrow_comp)

universe u

namespace DaggerModels.PartII.SimplicialSetLocalSystem

noncomputable section

variable {C : Type u} [Category.{u} C] (L : C ⥤ Type u)

/-- A chain with an element of the set attached to its first object. -/
def localSystem : SSet.{u} where
  obj q := Σ c : (nerve C).obj q, L.obj (first c)
  map {q r} α := fun x ↦
    ⟨(nerve C).map α x.1, L.map (initialArrow α x.1) x.2⟩
  map_id q := by
    funext x
    rcases x with ⟨c, t⟩
    dsimp only
    rw [initialArrow_id, L.map_id]
    rfl
  map_comp α β := by
    funext x
    rcases x with ⟨c, t⟩
    dsimp only
    rw [initialArrow_comp, L.map_comp]
    rfl

/-- Forget the value and retain the unchanged base chain. -/
def projection : localSystem L ⟶ nerve C where
  app q := fun x ↦ x.1
  naturality q r α := by
    funext x
    rfl

theorem projection_app (q : SimplexCategoryᵒᵖ)
    (x : (localSystem L).obj q) : (projection L).app q x = x.1 := rfl

/-- The first arrow in a fixed base simplex from its initial vertex to
the initial vertex of a chosen restricted simplex. -/
def firstArrow {n : ℕ} (A : Fin (n + 1) ⥤ C)
    {q : SimplexCategoryᵒᵖ} (t : (Δ[n] : SSet.{u}).obj q) :
    A.obj 0 ⟶ first (DaggerNativeOverNerveSimplexFamily.restrictChain A t) :=
  A.map (homOfLE (Fin.zero_le _))

/-- Restricting twice factors the initial transport through the
intermediate first vertex. -/
theorem firstArrow_comp {n : ℕ} (A : Fin (n + 1) ⥤ C)
    {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r)
    (t : (Δ[n] : SSet.{u}).obj q) :
    firstArrow A ((Δ[n] : SSet.{u}).map α t) =
      firstArrow A t ≫
        initialArrow α (DaggerNativeOverNerveSimplexFamily.restrictChain A t) := by
  change A.map _ = A.map _ ≫ A.map _
  rw [← A.map_comp]
  congr 1

#print axioms localSystem
#print axioms projection_app
#print axioms firstArrow_comp

end
end DaggerModels.PartII.SimplicialSetLocalSystem
