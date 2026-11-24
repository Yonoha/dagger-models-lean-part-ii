import DaggerModelsPartII.JTHigherGroupoidParameterPrism
import DaggerModelsPartII.NecklaceCylinderAugmentation

/-!
# Higher prisms in the actual reduced necklace cylinders
-/

set_option autoImplicit false

open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTHigherGraphPrismCylinder

open JTHigherInterleavedParameter JTHigherGroupoidParameterPrism JTParameterContraction
open JTNecklaceEndpointCylinder

noncomputable section

private abbrev J := GroupoidSimplex.parameter

/-- Keep the entire necklace coordinate while pairing its graph label with time. -/
def graphPrism {X : SSet.{0}} {k : SimplexCategory} (s : X ⟶ J.obj k)
    (n : SimplexCategory) : X ⊗ J.obj n ⟶ X ⊗ J.obj (common k n) :=
  lift (fst X (J.obj n)) ((s ⊗ₘ 𝟙 (J.obj n)) ≫ paired k n)

theorem graphPrism_natural {X Y : SSet.{0}} {k : SimplexCategory}
    (f : X ⟶ Y) (s : Y ⟶ J.obj k) (n : SimplexCategory) :
    (f ⊗ₘ 𝟙 (J.obj n)) ≫ graphPrism s n =
      graphPrism (f ≫ s) n ≫ (f ⊗ₘ 𝟙 (J.obj (common k n))) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [graphPrism, Category.assoc, tensorHom_fst, lift_fst, lift_fst_assoc]
  · simp only [graphPrism, Category.assoc, tensorHom_snd, lift_snd, Category.comp_id]
    rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]

theorem graphPrism_slice {X : SSet.{0}} {k : SimplexCategory}
    (s : X ⟶ J.obj k) (n : SimplexCategory) (t : Fin (n.len + 1)) :
    timeSlice X n t ≫ graphPrism s n = lift (𝟙 X) (s ≫ J.map (slice k n t)) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [timeSlice, graphPrism, Category.assoc, lift_fst]
  · simp only [Category.assoc, graphPrism, lift_snd]
    rw [← Category.assoc, timeSlice_natural, Category.assoc, paired_slice]

theorem graphPrism_ret {X : SSet.{0}} {k : SimplexCategory}
    (s : X ⟶ J.obj k) (n : SimplexCategory) :
    graphPrism s n ≫ (𝟙 X ⊗ₘ J.map (ret k n)) =
      fst X (J.obj n) ≫ lift (𝟙 X) s := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [graphPrism, Category.assoc, tensorHom_fst, lift_fst, Category.comp_id]
  · simp only [graphPrism, Category.assoc, tensorHom_snd, lift_snd, lift_snd_assoc]
    rw [paired_ret, tensorHom_fst]

/-- Over a constant old parameter, the entire time simplex is the
corresponding vertical simplex of the common parameter. -/
theorem graphPrism_constant {X : SSet.{0}} (k n : SimplexCategory) (a : Fin (k.len + 1)) :
    graphPrism (SSet.stdSimplex.isTerminalObj₀.from X ≫ parameterVertex k a) n =
      𝟙 X ⊗ₘ J.map (vertical k n a) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [graphPrism, lift_fst, tensorHom_fst, Category.comp_id]
  · simp only [graphPrism, lift_snd, tensorHom_snd]
    rw [← Category.id_comp (𝟙 (J.obj n)), ← tensorHom_comp_tensorHom, Category.assoc,
      paired_vertex, ← Category.assoc, tensorHom_snd, Category.comp_id]

theorem graphPrism_mapTime {X : SSet.{0}} {k n m : SimplexCategory}
    (s : X ⟶ J.obj k) (f : n ⟶ m) :
    graphPrism s n ≫ (X ◁ J.map (mapTime k f)) =
      (X ◁ J.map f) ≫ graphPrism s m := by
  simp only [← MonoidalCategory.id_tensorHom]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [graphPrism, Category.assoc, tensorHom_fst, lift_fst, Category.comp_id]
  · calc
      _ = (s ⊗ₘ 𝟙 (J.obj n)) ≫ paired k n ≫ J.map (mapTime k f) := by
        rw [Category.assoc, tensorHom_snd, ← Category.assoc, graphPrism,
          lift_snd, Category.assoc]
      _ = ((𝟙 X ⊗ₘ J.map f) ≫ (s ⊗ₘ 𝟙 (J.obj m))) ≫ paired k m := by
        rw [paired_mapTime, ← MonoidalCategory.id_tensorHom, ← Category.assoc,
          tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
          Category.comp_id, Category.id_comp, Category.id_comp, Category.comp_id]
      _ = _ := by rw [Category.assoc, Category.assoc, graphPrism, lift_snd]

private theorem graphPrism_boundary (T : NecklaceCode) {k : SimplexCategory}
    (s : T.toSSet ⟶ J.obj k) (n : SimplexCategory) :
    (endpointInclusion T ⊗ₘ 𝟙 (J.obj n)) ≫
        (graphPrism s n ≫ (cylinder T).app (common k n)) =
      fst JTXiEndpointCollapse.boundary (J.obj n) ≫ (boundary T).app (common k n) := by
  rw [← Category.assoc, graphPrism_natural, Category.assoc,
    (isPushout T (common k n)).w, ← Category.assoc, graphPrism, lift_fst]

/-- Descend the whole higher graph prism through the original two collapsed
ends of the actual reduced cylinder. -/
def cylinderMap (T : NecklaceCode) {k : SimplexCategory}
    (s : T.toSSet ⟶ J.obj k) (n : SimplexCategory) :
    (value T).obj n ⟶ (value T).obj (common k n) :=
  (isPushout T n).desc (graphPrism s n ≫ (cylinder T).app (common k n))
    ((boundary T).app (common k n)) (graphPrism_boundary T s n)

theorem cylinderMap_cylinder (T : NecklaceCode) {k : SimplexCategory}
    (s : T.toSSet ⟶ J.obj k) (n : SimplexCategory) :
    (cylinder T).app n ≫ cylinderMap T s n =
      graphPrism s n ≫ (cylinder T).app (common k n) :=
  (isPushout T n).inl_desc _ _ _

theorem cylinderMap_boundary (T : NecklaceCode) {k : SimplexCategory}
    (s : T.toSSet ⟶ J.obj k) (n : SimplexCategory) :
    (boundary T).app n ≫ cylinderMap T s n = (boundary T).app (common k n) :=
  (isPushout T n).inr_desc _ _ _

theorem cylinderMap_slice (T : NecklaceCode) {k : SimplexCategory}
    (s : T.toSSet ⟶ J.obj k) (n : SimplexCategory) (t : Fin (n.len + 1)) :
    (timeSlice T.toSSet n t ≫ (cylinder T).app n) ≫ cylinderMap T s n =
      lift (𝟙 T.toSSet) (s ≫ J.map (slice k n t)) ≫ (cylinder T).app (common k n) := by
  rw [Category.assoc, cylinderMap_cylinder, ← Category.assoc, graphPrism_slice]

/-- The descended prism commutes with every simplex operator in the time
coordinate, including on the actual ordered boundary. -/
theorem cylinderMap_mapTime (T : NecklaceCode) {k n m : SimplexCategory}
    (s : T.toSSet ⟶ J.obj k) (f : n ⟶ m) :
    cylinderMap T s n ≫ (value T).map (mapTime k f) =
      (value T).map f ≫ cylinderMap T s m := by
  have hC {a b : SimplexCategory} (g : a ⟶ b) :
      (T.toSSet ◁ J.map g) ≫ (cylinder T).app b =
        (cylinder T).app a ≫ (value T).map g :=
    (cylinder T).naturality g
  have hB {a b : SimplexCategory} (g : a ⟶ b) :
      (boundary T).app a ≫ (value T).map g = (boundary T).app b := by
    rw [← (boundary T).naturality g]
    exact Category.id_comp _
  apply (isPushout T n).hom_ext
  · rw [← Category.assoc, cylinderMap_cylinder, Category.assoc, ← hC,
      ← Category.assoc, graphPrism_mapTime, Category.assoc,
      ← Category.assoc ((cylinder T).app n), ← hC, Category.assoc,
      cylinderMap_cylinder]
  · rw [← Category.assoc, cylinderMap_boundary, hB,
      ← Category.assoc, hB, cylinderMap_boundary]

end

end DaggerModels.PartII.JTHigherGraphPrismCylinder
