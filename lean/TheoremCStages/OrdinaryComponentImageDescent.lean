import OrdinarySegalComponentImage

/-!
# Descent into an actual component image

If a map lands in a specified component image after precomposition by a map
surjective on connected components, it already lands in that component image.
The factor retains the original map exactly. No weak equivalence of the
factor, or reflection of components under another map, is asserted.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.OrdinaryComponentImageDescent

open OrdinarySegalComponentImage (componentImage imageComponents)
open OrdinarySegalComponentSubcomplex (mem_selected_iff simplexComponent_map)

noncomputable section

/-- Component-surjective precomposition detects membership in the actual image. -/
theorem lands_in_image {A B X Y : SSet.{0}} (a : A ⟶ B) (b : B ⟶ Y)
    (c : A ⟶ X) (f : X ⟶ Y) (h : a ≫ b = c ≫ f)
    (ha : Function.Surjective (SSet.mapπ₀ a)) :
    ∀ q (y : B.obj q), b.app q y ∈ (componentImage f).obj q := by
  intro q y
  rw [componentImage, mem_selected_iff, simplexComponent_map]
  obtain ⟨d, hd⟩ := ha (DaggerUnitaryDiscrete.simplexComponent B q y)
  refine ⟨SSet.mapπ₀ c d, ?_⟩
  have ht := congrFun (congrArg SSet.mapπ₀ h) d
  simpa only [SSet.mapπ₀_comp_apply, hd] using ht.symm

/-- Descend the literal whole map to the specified component-saturated image. -/
def factor {A B X Y : SSet.{0}} (a : A ⟶ B) (b : B ⟶ Y)
    (c : A ⟶ X) (f : X ⟶ Y) (h : a ≫ b = c ≫ f)
    (ha : Function.Surjective (SSet.mapπ₀ a)) :
    B ⟶ (componentImage f).toSSet :=
  SSet.Subcomplex.lift b (by
    intro q y hy
    obtain ⟨x, rfl⟩ := hy
    exact lands_in_image a b c f h ha q x)

/-- The descended map has exactly the original map after inclusion. -/
theorem factor_inclusion {A B X Y : SSet.{0}} (a : A ⟶ B) (b : B ⟶ Y)
    (c : A ⟶ X) (f : X ⟶ Y) (h : a ≫ b = c ≫ f)
    (ha : Function.Surjective (SSet.mapπ₀ a)) :
    factor a b c f h ha ≫ (componentImage f).ι = b :=
  SSet.Subcomplex.lift_ι _ _

#print axioms lands_in_image
#print axioms factor
#print axioms factor_inclusion

end

end DaggerModels.PartII.OrdinaryComponentImageDescent
