import DaggerModelsPartII.JTInterpolatedReducedCylinder

/-!
# Time reindexing of interpolated reduced cylinders
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace
open DaggerModels.PartII.JTNecklaceEndpointCylinder
open DaggerModels.PartII.JTInterpolatedReducedCylinder
open DaggerModels.PartII.JTCodiscreteParameterPairing

namespace DaggerModels.PartII.JTInterpolatedCylinderReindex

noncomputable section

private abbrev J := GroupoidSimplex.parameter

/-- Vertexwise interpolation respects every map of time simplices. -/
theorem interpolate_reindex {X : SSet.{0}} {k m n : SimplexCategory}
    (j : m ⟶ n) (s : Fin (n.len + 1) → (X ⟶ J.obj k)) :
    (𝟙 X ⊗ₘ J.map j) ≫ JTGraphParameterInterpolation.interpolate s =
      JTGraphParameterInterpolation.interpolate (fun i ↦ s (j.toOrderHom i)) := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z v
  change coord k q
      ((JTGraphParameterInterpolation.interpolate s).app q
        (z.1, (J.map j).app q z.2)) v =
    coord k q
      ((JTGraphParameterInterpolation.interpolate (fun i ↦ s (j.toOrderHom i))).app q z) v
  rw [JTGraphParameterInterpolation.coord_interpolate,
    JTGraphParameterInterpolation.coord_interpolate, coord_map]

/-- The reduced map commutes with every time reindexing map. -/
theorem cylinderMap_reindex (T : NecklaceCode) {k m n : SimplexCategory}
    (j : m ⟶ n) (p : T.toSSet ⊗ J.obj n ⟶ J.obj k) :
    (value T).map j ≫ cylinderMap T p =
      cylinderMap T ((𝟙 T.toSSet ⊗ₘ J.map j) ≫ p) := by
  apply (isPushout T m).hom_ext
  · rw [← Category.assoc, ← (cylinder T).naturality j,
      Category.assoc, cylinderMap_cylinder, cylinderMap_cylinder]
    change ((𝟙 T.toSSet ⊗ₘ J.map j) ≫
        lift (fst T.toSSet (J.obj n)) p) ≫ (cylinder T).app k =
      lift (fst T.toSSet (J.obj m)) ((𝟙 T.toSSet ⊗ₘ J.map j) ≫ p) ≫
        (cylinder T).app k
    have h : (𝟙 T.toSSet ⊗ₘ J.map j) ≫
        lift (fst T.toSSet (J.obj n)) p =
      lift (fst T.toSSet (J.obj m)) ((𝟙 T.toSSet ⊗ₘ J.map j) ≫ p) := by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc, lift_fst, tensorHom_fst, Category.comp_id]
      · simp only [Category.assoc, lift_snd]
    rw [h]
  · rw [← Category.assoc, ← (boundary T).naturality j]
    change (𝟙 _ ≫ (boundary T).app n) ≫ cylinderMap T p = _
    rw [Category.id_comp, cylinderMap_boundary, cylinderMap_boundary]

/-- The interpolated reduced-cylinder map is strictly natural in time. -/
theorem interpolated_reindex (T : NecklaceCode) {k m n : SimplexCategory}
    (j : m ⟶ n)
    (s : Fin (n.len + 1) → (T.toSSet ⟶ J.obj k)) :
    (value T).map j ≫
        cylinderMap T (JTGraphParameterInterpolation.interpolate s) =
      cylinderMap T
        (JTGraphParameterInterpolation.interpolate (fun i ↦ s (j.toOrderHom i))) := by
  rw [cylinderMap_reindex, interpolate_reindex]

end

end DaggerModels.PartII.JTInterpolatedCylinderReindex
