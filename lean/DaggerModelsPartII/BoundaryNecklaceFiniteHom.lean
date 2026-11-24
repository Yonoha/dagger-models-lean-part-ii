import DaggerModelsPartII.BoundaryNecklaceComma
import ChosenNecklaceMapVertices

/-! Operator finiteness for actual necklace presentations of finite-index cylinders. -/

set_option autoImplicit false

open CategoryTheory Limits
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.BoundaryNecklaceComma

noncomputable section

private theorem finite_necklace_hom (S T : NecklaceCode) : Finite (S ⟶ T) := by
  apply Finite.of_injective
    (f := fun (g : S ⟶ T) ↦ NecklaceCode.mapVertices g.map)
  intro g h e
  apply NecklaceCode.Hom.ext
  exact NecklaceCode.hom_ext_vertices g.map h.map e

variable {J : Type} [SmallCategory J]
variable (F : J ⥤ Under JTXiEndpointCollapse.boundary)

/-- Every presentation arrow is determined by its base operator and its internal
necklace operator. Finite base hom sets therefore give finite presentation hom sets. -/
theorem finite_hom (hJ : ∀ i j : J, Finite (i ⟶ j))
    (P P' : Presentation F) : Finite (P ⟶ P') := by
  letI := hJ P.base P'.base
  letI := finite_necklace_hom P.fiber.left P'.fiber.left
  let op : (P ⟶ P') → (P.base ⟶ P'.base) × (P.fiber.left ⟶ P'.fiber.left) :=
    fun f ↦ (f.base, f.fiber.left)
  apply Finite.of_injective op
  intro f g e
  have hb : f.base = g.base := congrArg Prod.fst e
  have hk : f.fiber.left = g.fiber.left := congrArg Prod.snd e
  rcases f with ⟨a, f⟩
  rcases g with ⟨b, g⟩
  change a = b at hb
  subst b
  refine Grothendieck.ext _ _ rfl ?_
  simp only [eqToHom_refl, Category.id_comp]
  apply CostructuredArrow.hom_ext
  exact hk

end
end DaggerModels.PartII.BoundaryNecklaceComma
