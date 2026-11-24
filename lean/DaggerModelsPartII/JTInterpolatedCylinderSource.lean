import DaggerModelsPartII.JTInterpolatedReducedCylinder

/-!
# Source naturality of interpolated reduced necklace cylinders
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace
open DaggerModels.PartII.JTNecklaceEndpointCylinder
open DaggerModels.PartII.JTInterpolatedReducedCylinder
open DaggerModels.PartII.JTCodiscreteParameterPairing

namespace DaggerModels.PartII.JTInterpolatedCylinderSource

noncomputable section

private abbrev J := GroupoidSimplex.parameter

/-- Vertexwise interpolation is natural in its horizontal source. -/
theorem interpolate_source {X' X : SSet.{0}} {k n : SimplexCategory}
    (g : X' ⟶ X) (s : Fin (n.len + 1) → (X ⟶ J.obj k)) :
    (g ⊗ₘ 𝟙 (J.obj n)) ≫ JTGraphParameterInterpolation.interpolate s =
      JTGraphParameterInterpolation.interpolate (fun i ↦ g ≫ s i) := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z v
  change coord k q
      ((JTGraphParameterInterpolation.interpolate s).app q
        (g.app q z.1, z.2)) v =
    coord k q
      ((JTGraphParameterInterpolation.interpolate (fun i ↦ g ≫ s i)).app q z) v
  rw [JTGraphParameterInterpolation.coord_interpolate,
    JTGraphParameterInterpolation.coord_interpolate]
  rfl

/-- A native necklace map commutes with arbitrary reduced-cylinder graphs. -/
theorem cylinderMap_source {S T : NecklaceCode} (f : S ⟶ T)
    {k n : SimplexCategory} (p : T.toSSet ⊗ J.obj n ⟶ J.obj k) :
    cylinderMap S ((f.map ⊗ₘ 𝟙 (J.obj n)) ≫ p) ≫ nativeMap f k =
      nativeMap f n ≫ cylinderMap T p := by
  apply (isPushout S n).hom_ext
  · rw [← Category.assoc, cylinderMap_cylinder, Category.assoc,
      nativeMap_cylinder]
    rw [← Category.assoc ((cylinder S).app n) (nativeMap f n) (cylinderMap T p),
      nativeMap_cylinder, Category.assoc, cylinderMap_cylinder]
    have h : lift (fst S.toSSet (J.obj n))
        ((f.map ⊗ₘ 𝟙 (J.obj n)) ≫ p) ≫
        (f.map ⊗ₘ 𝟙 (J.obj k)) =
      (f.map ⊗ₘ 𝟙 (J.obj n)) ≫
        lift (fst T.toSSet (J.obj n)) p := by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc, tensorHom_fst, lift_fst]
        rw [← Category.assoc, lift_fst]
      · simp only [Category.assoc, tensorHom_snd, lift_snd, Category.comp_id]
    simpa only [Category.assoc] using
      congrArg (fun u ↦ u ≫ (cylinder T).app k) h
  · rw [← Category.assoc, cylinderMap_boundary, nativeMap_boundary,
      ← Category.assoc, nativeMap_boundary, cylinderMap_boundary]

/-- A native necklace map commutes with interpolated reduced-cylinder graphs. -/
theorem interpolated_source {S T : NecklaceCode} (f : S ⟶ T)
    {k n : SimplexCategory}
    (s : Fin (n.len + 1) → (T.toSSet ⟶ J.obj k)) :
    cylinderMap S
        (JTGraphParameterInterpolation.interpolate (fun i ↦ f.map ≫ s i)) ≫
        nativeMap f k =
      nativeMap f n ≫ cylinderMap T (JTGraphParameterInterpolation.interpolate s) := by
  rw [← interpolate_source, cylinderMap_source]

end

end DaggerModels.PartII.JTInterpolatedCylinderSource
