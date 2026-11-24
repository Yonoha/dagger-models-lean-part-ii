import DaggerModelsPartII.JTGraphParameterInterpolation
import DaggerModelsPartII.JTNecklaceCylinderConnector
import DaggerModelsPartII.NecklaceCylinderJointDiagram
import DaggerModelsPartII.BoundaryNecklaceComma
import DaggerModelsPartII.JTParameterBlocks

/-!
# Interpolation in an actual reduced necklace cylinder
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace
open DaggerModels.PartII.JTNecklaceEndpointCylinder
open DaggerModels.PartII.NecklaceCylinderAugmentation
open DaggerModels.PartII.JTParameterContraction

namespace DaggerModels.PartII.JTInterpolatedReducedCylinder

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev B := JTXiEndpointCollapse.boundary

private theorem cylinderMap_boundary_compatibility (T : NecklaceCode)
    {k n : SimplexCategory} (p : T.toSSet ⊗ J.obj n ⟶ J.obj k) :
    (endpointInclusion T ⊗ₘ 𝟙 (J.obj n)) ≫
        (lift (fst T.toSSet (J.obj n)) p ≫ (cylinder T).app k) =
      fst B (J.obj n) ≫ (boundary T).app k := by
  have h : (endpointInclusion T ⊗ₘ 𝟙 (J.obj n)) ≫
      lift (fst T.toSSet (J.obj n)) p =
      lift (fst B (J.obj n) ≫ endpointInclusion T)
        ((endpointInclusion T ⊗ₘ 𝟙 (J.obj n)) ≫ p) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, tensorHom_fst]
    · simp only [Category.assoc, lift_snd]
  rw [← Category.assoc, h]
  exact JTNecklaceCylinderConnector.boundary_collapse T k
    (fst B (J.obj n)) ((endpointInclusion T ⊗ₘ 𝟙 (J.obj n)) ≫ p)

/-- A graph over any parameter degree descends through the actual pushout. -/
def cylinderMap (T : NecklaceCode) {k n : SimplexCategory}
    (p : T.toSSet ⊗ J.obj n ⟶ J.obj k) :
    (value T).obj n ⟶ (value T).obj k :=
  (isPushout T n).desc
    (lift (fst T.toSSet (J.obj n)) p ≫ (cylinder T).app k)
    ((boundary T).app k) (cylinderMap_boundary_compatibility T p)

theorem cylinderMap_cylinder (T : NecklaceCode) {k n : SimplexCategory}
    (p : T.toSSet ⊗ J.obj n ⟶ J.obj k) :
    (cylinder T).app n ≫ cylinderMap T p =
      lift (fst T.toSSet (J.obj n)) p ≫ (cylinder T).app k :=
  (isPushout T n).inl_desc _ _ _

theorem cylinderMap_boundary (T : NecklaceCode) {k n : SimplexCategory}
    (p : T.toSSet ⊗ J.obj n ⟶ J.obj k) :
    (boundary T).app n ≫ cylinderMap T p = (boundary T).app k :=
  (isPushout T n).inr_desc _ _ _

private theorem slice_boundary (T : NecklaceCode) (n : SimplexCategory)
    (i : Fin (n.len + 1)) :
    endpointInclusion T ≫
        (lift (𝟙 T.toSSet)
          (SSet.stdSimplex.isTerminalObj₀.from T.toSSet ≫ parameterVertex n i) ≫
          (cylinder T).app n) = (boundary T).app n := by
  have h : endpointInclusion T ≫
      lift (𝟙 T.toSSet)
        (SSet.stdSimplex.isTerminalObj₀.from T.toSSet ≫ parameterVertex n i) =
      lift (𝟙 B ≫ endpointInclusion T)
        (endpointInclusion T ≫
          (SSet.stdSimplex.isTerminalObj₀.from T.toSSet ≫ parameterVertex n i)) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, Category.comp_id, Category.id_comp]
    · simp only [Category.assoc, lift_snd]
  rw [← Category.assoc, h]
  rw [JTNecklaceCylinderConnector.boundary_collapse]
  exact (Category.id_comp _).symm

/-- A time vertex gives a map of the original necklace under its boundary. -/
def slice (T : NecklaceCode) (n : SimplexCategory) (i : Fin (n.len + 1)) :
    BoundaryNecklaceComma.necklaceUnder.obj T ⟶ (under T).obj n :=
  Under.homMk
    (lift (𝟙 T.toSSet)
      (SSet.stdSimplex.isTerminalObj₀.from T.toSSet ≫ parameterVertex n i) ≫
      (cylinder T).app n)
    (slice_boundary T n i)

theorem slice_augmentation (T : NecklaceCode) (n : SimplexCategory)
    (i : Fin (n.len + 1)) :
    (slice T n i).right ≫ augmentation T n = 𝟙 T.toSSet := by
  change (lift (𝟙 T.toSSet)
    (SSet.stdSimplex.isTerminalObj₀.from T.toSSet ≫ parameterVertex n i) ≫
    (cylinder T).app n) ≫ augmentation T n = 𝟙 T.toSSet
  rw [Category.assoc, augmentation_cylinder, lift_fst]

/-- Time slices commute with every simplex operator on the parameter. -/
theorem slice_reindex (T : NecklaceCode) {n m : SimplexCategory}
    (f : n ⟶ m) (i : Fin (n.len + 1)) :
    slice T n i ≫ (under T).map f = slice T m (f.toOrderHom i) := by
  apply Under.UnderMorphism.ext
  change (lift (𝟙 T.toSSet)
      (SSet.stdSimplex.isTerminalObj₀.from T.toSSet ≫ parameterVertex n i) ≫
      (cylinder T).app n) ≫ (value T).map f =
    lift (𝟙 T.toSSet)
      (SSet.stdSimplex.isTerminalObj₀.from T.toSSet ≫
        parameterVertex m (f.toOrderHom i)) ≫ (cylinder T).app m
  rw [Category.assoc, ← (cylinder T).naturality f, ← Category.assoc]
  change (lift (𝟙 T.toSSet)
      (SSet.stdSimplex.isTerminalObj₀.from T.toSSet ≫ parameterVertex n i) ≫
      (𝟙 T.toSSet ⊗ₘ J.map f)) ≫ (cylinder T).app m = _
  have h : lift (𝟙 T.toSSet)
      (SSet.stdSimplex.isTerminalObj₀.from T.toSSet ≫ parameterVertex n i) ≫
      (𝟙 T.toSSet ⊗ₘ J.map f) =
      lift (𝟙 T.toSSet)
        (SSet.stdSimplex.isTerminalObj₀.from T.toSSet ≫
          (parameterVertex n i ≫ J.map f)) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, tensorHom_fst, lift_fst, Category.comp_id]
    · simp only [Category.assoc, tensorHom_snd]
      rw [← Category.assoc, lift_snd]
      rw [lift_snd, Category.assoc]
  rw [h, JTParameterBlocks.parameterVertex_map]

theorem slice_map_interpolate (T : NecklaceCode) {k n : SimplexCategory}
    (s : Fin (n.len + 1) → (T.toSSet ⟶ J.obj k))
    (i : Fin (n.len + 1)) :
    (slice T n i).right ≫
        cylinderMap T (JTGraphParameterInterpolation.interpolate s) =
      lift (𝟙 T.toSSet) (s i) ≫ (cylinder T).app k := by
  change (lift (𝟙 T.toSSet)
    (SSet.stdSimplex.isTerminalObj₀.from T.toSSet ≫ parameterVertex n i) ≫
    (cylinder T).app n) ≫
      cylinderMap T (JTGraphParameterInterpolation.interpolate s) = _
  rw [Category.assoc, cylinderMap_cylinder, ← Category.assoc]
  have h : lift (𝟙 T.toSSet)
      (SSet.stdSimplex.isTerminalObj₀.from T.toSSet ≫ parameterVertex n i) ≫
      lift (fst T.toSSet (J.obj n)) (JTGraphParameterInterpolation.interpolate s) =
      lift (𝟙 T.toSSet)
        (lift (𝟙 T.toSSet)
          (SSet.stdSimplex.isTerminalObj₀.from T.toSSet ≫ parameterVertex n i) ≫
          JTGraphParameterInterpolation.interpolate s) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst]
    · simp only [Category.assoc, lift_snd]
  rw [h]
  rw [JTGraphParameterInterpolation.slice_interpolate]

end

end DaggerModels.PartII.JTInterpolatedReducedCylinder
