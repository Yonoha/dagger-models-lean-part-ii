import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import TopCatModelCategory.SSet.Finite
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! A finite simplicial support in a nerve lies in a finite-object full subcategory. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.NerveVertexSupport

noncomputable section

variable {C : Type} [SmallCategory C] (A : (nerve C).Subcomplex)

/-- The objects appearing as vertices of the given support. -/
def present : ObjectProperty C :=
  fun c ↦ ∃ v : A.toSSet.obj (op ⦋0⦌), nerveEquiv v.val = c

/-- The full category on the actual vertices of a finite support has finitely many objects. -/
theorem finite_objects (hA : A.toSSet.IsFinite) : Finite (present A).FullSubcategory := by
  letI := hA
  let f : A.toSSet.obj (op ⦋0⦌) → (present A).FullSubcategory :=
    fun v ↦ ⟨nerveEquiv v.val, ⟨v, rfl⟩⟩
  apply Finite.of_surjective f
  rintro ⟨c, v, h⟩
  subst c
  exact ⟨v, rfl⟩

private theorem vertex_present (n : SimplexCategoryᵒᵖ) (s : A.toSSet.obj n)
    (i : Fin (n.unop.len + 1)) : present A (s.val.obj i) := by
  refine ⟨A.toSSet.map (SimplexCategory.const ⦋0⦌ n.unop i).op s, ?_⟩
  rfl

/-- Restrict every composable chain in the support to the full category of its vertices. -/
def lift : A.toSSet ⟶ nerve (present A).FullSubcategory where
  app n s := (present A).lift s.val (vertex_present A n s)
  naturality _ _ _ := rfl

/-- The restriction changes neither the simplex nor any of its arrows in the ambient nerve. -/
theorem lift_ι : lift A ≫ nerveMap (present A).ι = A.ι := rfl

end
end DaggerModels.PartII.NerveVertexSupport
