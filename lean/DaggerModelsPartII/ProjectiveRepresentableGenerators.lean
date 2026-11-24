import DaggerModelsPartII.ProjectiveKanDiagram
import DaggerModelsPartII.IndexKanExtensions

/-!
# Free projective cells and representable products

The free diagram at `op c` is the coproduct of one copy of the coefficient
at every arrow into `c`. This gives an exact componentwise presentation of
the projective boundary and horn generators used in the manuscript.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite

universe u

namespace DaggerModels.PartII.ProjectiveRepresentableGenerators

variable {C : Type u} [SmallCategory C] (c d : C)

noncomputable section

/-- The free diagram is pointwise the hom-indexed coproduct. -/
theorem free_obj_obj (K : SSet.{u}) :
    ((ProjectiveKanDiagram.free Cᵒᵖ (op c)).obj K).obj (op d) =
      ∐ fun _ : (op c ⟶ op d) ↦ K := rfl

/-- A map of coefficients acts on every summand by the same map. -/
theorem free_map_app {K L : SSet.{u}} (f : K ⟶ L) :
    ((ProjectiveKanDiagram.free Cᵒᵖ (op c)).map f).app (op d) =
      Limits.Sigma.map (fun _ : (op c ⟶ op d) ↦ f) := by
  apply Limits.Sigma.hom_ext
  intro h
  simp [ProjectiveKanDiagram.free, evaluationLeftAdjoint]

/-- The projective boundary generator has the claimed hom-indexed component. -/
theorem boundary_generator_app (n : ℕ) :
    ((ProjectiveKanDiagram.free Cᵒᵖ (op c)).map (SSet.boundary n).ι).app (op d) =
      Limits.Sigma.map (fun _ : (op c ⟶ op d) ↦ (SSet.boundary n).ι) :=
  free_map_app (c := c) (d := d) _

/-- The projective horn generator has the claimed hom-indexed component. -/
theorem horn_generator_app (n : ℕ) (i : Fin (n + 2)) :
    ((ProjectiveKanDiagram.free Cᵒᵖ (op c)).map (SSet.horn (n + 1) i).ι).app (op d) =
      Limits.Sigma.map (fun _ : (op c ⟶ op d) ↦ (SSet.horn (n + 1) i).ι) :=
  free_map_app (c := c) (d := d) _

end

end DaggerModels.PartII.ProjectiveRepresentableGenerators
