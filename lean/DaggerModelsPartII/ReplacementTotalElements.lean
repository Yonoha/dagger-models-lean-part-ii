import NativeSimplicialReplacement
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Functor.Currying

/-!
# The actual first-object map from diagonal-bar simplices to total elements

The original replacement chain and its entire parameter simplex are retained.
The map is a functor; no weakness or comma-category contraction is assumed.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerNativeSimplicialReplacement DaggerNativeSimplicialReplacementCells
open scoped Prod

universe u

namespace DaggerModels.PartII.ReplacementTotalElements

noncomputable section

variable {C : Type u} [Category.{u} C] (G : C ⥤ SSet.{u})

/-- The SAME original diagonal simplicial replacement. -/
abbrev bar : SSet.{u} := DaggerBisimplicialDiagonal.diag (replacement G)

/-- Uncurry the original weight without forgetting either operator. -/
def totalPresheaf : C × SimplexCategoryᵒᵖ ⥤ Type u := Functor.uncurry.obj G

/-- A bar simplex determines its literal first-object total label. -/
def totalObject (i : (bar G).Elements) : (totalPresheaf G).Elements :=
  ⟨(first i.2.1, i.1), i.2.2⟩

/-- A simplex operator gives the original initial chain arrow and that SAME
operator, followed only by the supplied literal bar-cell equality. -/
def totalMap {i j : (bar G).Elements} (f : i ⟶ j) :
    totalObject G i ⟶ totalObject G j := by
  rcases i with ⟨q, v⟩
  rcases j with ⟨r, w⟩
  rcases f with ⟨α, h⟩
  change q ⟶ r at α
  change (bar G).map α v = w at h
  subst w
  exact ⟨initialArrow α v.1 ×ₘ α, rfl⟩

private theorem totalMap_val {i j : (bar G).Elements} (f : i ⟶ j) :
    (totalMap G f).val =
      (initialArrow f.val i.2.1 ×ₘ f.val) ≫
        eqToHom (congrArg (fun w : (bar G).obj j.1 ↦ (first w.1, j.1)) f.property) := by
  rcases i with ⟨q, v⟩
  rcases j with ⟨r, w⟩
  rcases f with ⟨α, h⟩
  change q ⟶ r at α
  change (bar G).map α v = w at h
  subst w
  simp only [totalMap, eqToHom_refl, Category.comp_id]
  rfl

private theorem totalMap_id (i : (bar G).Elements) :
    totalMap G (𝟙 i) = 𝟙 (totalObject G i) := by
  rcases i with ⟨q, v⟩
  apply Subtype.ext
  rw [totalMap_val]
  change (initialArrow (𝟙 q) v.1 ×ₘ 𝟙 q) ≫ eqToHom _ = 𝟙 _
  simp only [initialArrow_id, eqToHom_refl, Category.comp_id]
  rfl

private theorem totalMap_comp {i j k : (bar G).Elements} (f : i ⟶ j) (g : j ⟶ k) :
    totalMap G (f ≫ g) = totalMap G f ≫ totalMap G g := by
  rcases i with ⟨q, v⟩
  rcases j with ⟨r, w⟩
  rcases k with ⟨s, t⟩
  rcases f with ⟨α, h⟩
  rcases g with ⟨β, h'⟩
  change q ⟶ r at α
  change r ⟶ s at β
  change (bar G).map α v = w at h
  subst w
  change (bar G).map β ((bar G).map α v) = t at h'
  subst t
  apply Subtype.ext
  simp only [totalMap_val, CategoryOfElements.comp_val]
  change (initialArrow (α ≫ β) v.1 ×ₘ (α ≫ β)) ≫ eqToHom _ =
    ((initialArrow α v.1 ×ₘ α) ≫ eqToHom _) ≫
      ((initialArrow β ((bar G).map α v).1 ×ₘ β) ≫ eqToHom _)
  simp only [eqToHom_refl, Category.comp_id]
  change (initialArrow (α ≫ β) v.1 ×ₘ (α ≫ β)) =
    ((initialArrow α v.1 ≫ initialArrow β ((nerve C).map α v.1)) ×ₘ (α ≫ β))
  rw [initialArrow_comp]

/-- The actual all-operator map from bar elements to total label elements. -/
def toTotal : (bar G).Elements ⥤ (totalPresheaf G).Elements where
  obj := totalObject G
  map := totalMap G
  map_id := totalMap_id G
  map_comp := totalMap_comp G

/-- Its opposite has precisely the forward decorated operator direction. -/
def toTotalOp : (bar G).Elementsᵒᵖ ⥤ (totalPresheaf G).Elementsᵒᵖ :=
  (toTotal G).op

end

end DaggerModels.PartII.ReplacementTotalElements
