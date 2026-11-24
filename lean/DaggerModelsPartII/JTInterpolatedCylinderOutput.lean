import DaggerModelsPartII.JTInterpolatedCylinderSource
import DaggerModelsPartII.JTInterpolatedCylinderReindex

/-!
# Output naturality of interpolated reduced necklace cylinders
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace
open DaggerModels.PartII.JTNecklaceEndpointCylinder
open DaggerModels.PartII.JTInterpolatedReducedCylinder
open DaggerModels.PartII.JTCodiscreteParameterPairing

namespace DaggerModels.PartII.JTInterpolatedCylinderOutput

noncomputable section

private abbrev J := GroupoidSimplex.parameter

/-- Vertexwise interpolation is natural in its output parameter. -/
theorem interpolate_output {X : SSet.{0}} {k l n : SimplexCategory}
    (j : k ⟶ l) (s : Fin (n.len + 1) → (X ⟶ J.obj k)) :
    JTGraphParameterInterpolation.interpolate s ≫ J.map j =
      JTGraphParameterInterpolation.interpolate (fun i ↦ s i ≫ J.map j) := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z v
  change coord l q
      ((J.map j).app q ((JTGraphParameterInterpolation.interpolate s).app q z)) v =
    coord l q
      ((JTGraphParameterInterpolation.interpolate (fun i ↦ s i ≫ J.map j)).app q z) v
  rw [coord_map, JTGraphParameterInterpolation.coord_interpolate,
    JTGraphParameterInterpolation.coord_interpolate]
  change j.toOrderHom (coord k q ((s (coord n q z.2 v)).app q z.1) v) =
    coord l q ((J.map j).app q ((s (coord n q z.2 v)).app q z.1)) v
  rw [coord_map]

/-- A reduced-cylinder graph commutes with output parameter maps. -/
theorem cylinderMap_output (T : NecklaceCode) {k l n : SimplexCategory}
    (j : k ⟶ l) (p : T.toSSet ⊗ J.obj n ⟶ J.obj k) :
    cylinderMap T p ≫ (value T).map j = cylinderMap T (p ≫ J.map j) := by
  apply (isPushout T n).hom_ext
  · rw [← Category.assoc, cylinderMap_cylinder, Category.assoc,
      ← (cylinder T).naturality j]
    rw [← Category.assoc, cylinderMap_cylinder]
    change (lift (fst T.toSSet (J.obj n)) p ≫
        (𝟙 T.toSSet ⊗ₘ J.map j)) ≫ (cylinder T).app l =
      lift (fst T.toSSet (J.obj n)) (p ≫ J.map j) ≫ (cylinder T).app l
    have h : lift (fst T.toSSet (J.obj n)) p ≫
        (𝟙 T.toSSet ⊗ₘ J.map j) =
      lift (fst T.toSSet (J.obj n)) (p ≫ J.map j) := by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc, tensorHom_fst, lift_fst, Category.comp_id]
      · simp only [Category.assoc, tensorHom_snd]
        rw [← Category.assoc, lift_snd]
        rw [lift_snd]
    rw [h]
  · rw [← Category.assoc, cylinderMap_boundary,
      ← (boundary T).naturality j, cylinderMap_boundary]
    simp

/-- The interpolated graph and its reduced-cylinder map are both natural in output. -/
theorem interpolated_output (T : NecklaceCode) {k l n : SimplexCategory}
    (j : k ⟶ l) (s : Fin (n.len + 1) → (T.toSSet ⟶ J.obj k)) :
    (JTGraphParameterInterpolation.interpolate s ≫ J.map j =
        JTGraphParameterInterpolation.interpolate (fun i ↦ s i ≫ J.map j)) ∧
      (cylinderMap T (JTGraphParameterInterpolation.interpolate s) ≫ (value T).map j =
        cylinderMap T
          (JTGraphParameterInterpolation.interpolate (fun i ↦ s i ≫ J.map j))) := by
  constructor
  · exact interpolate_output j s
  · rw [cylinderMap_output, interpolate_output]

end

end DaggerModels.PartII.JTInterpolatedCylinderOutput
