import DaggerModelsPartII.JTGroupoidParameterPrism
import DaggerModelsPartII.NecklaceCylinderAugmentation

/-!
# Prism maps between the actual reduced necklace cylinders
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphPrismCylinder

open JTInterleavedParameter JTGroupoidParameterPrism JTParameterContraction
open JTNecklaceEndpointCylinder

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev I := J.obj ⦋1⦌
private abbrev K := common

/-- Keep the horizontal coordinate and pair the old parameter with time. -/
def graphPrism {X : SSet.{0}} {k : SimplexCategory} (s : X ⟶ J.obj k) :
    X ⊗ I ⟶ X ⊗ J.obj (K k) :=
  lift (fst X I) ((s ⊗ₘ 𝟙 I) ≫ paired k)

theorem graphPrism_natural {X Y : SSet.{0}} {k : SimplexCategory}
    (f : X ⟶ Y) (s : Y ⟶ J.obj k) :
    (f ⊗ₘ 𝟙 I) ≫ graphPrism s =
      graphPrism (f ≫ s) ≫ (f ⊗ₘ 𝟙 (J.obj (K k))) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [graphPrism, Category.assoc, tensorHom_fst, lift_fst,
      lift_fst_assoc]
  · simp only [graphPrism, Category.assoc, tensorHom_snd, lift_snd,
      Category.comp_id]
    rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]

theorem graphPrism_slice {X : SSet.{0}} {k : SimplexCategory}
    (s : X ⟶ J.obj k) (t : Fin 2) :
    timeSlice X t ≫ graphPrism s = lift (𝟙 X) (s ≫ J.map (slice k t)) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, graphPrism, lift_fst, timeSlice_fst, lift_fst]
  · simp only [Category.assoc, graphPrism, lift_snd]
    rw [← Category.assoc, timeSlice_natural, Category.assoc, paired_slice]

/-- Forgetting time on the parameter recovers the whole original graph. -/
theorem graphPrism_ret {X : SSet.{0}} {k : SimplexCategory} (s : X ⟶ J.obj k) :
    graphPrism s ≫ (𝟙 X ⊗ₘ J.map (ret k)) = fst X I ≫ lift (𝟙 X) s := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [graphPrism, Category.assoc, tensorHom_fst, lift_fst,
      Category.comp_id]
  · simp only [graphPrism, Category.assoc, tensorHom_snd, lift_snd, lift_snd_assoc]
    rw [paired_ret, tensorHom_fst]

/-- A constant old parameter traverses its duplicate edge in the prism. -/
theorem graphPrism_constant {X : SSet.{0}} (k : SimplexCategory)
    (a : Fin (k.len + 1)) :
    graphPrism (SSet.stdSimplex.isTerminalObj₀.from X ≫ parameterVertex k a) =
      𝟙 X ⊗ₘ J.map (edge k a) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [graphPrism, lift_fst, tensorHom_fst, Category.comp_id]
  · simp only [graphPrism, lift_snd, tensorHom_snd]
    rw [← Category.id_comp (𝟙 I), ← tensorHom_comp_tensorHom, Category.assoc,
      paired_vertex, ← Category.assoc, tensorHom_snd, Category.comp_id]

private theorem graphPrism_boundary (T : NecklaceCode) {k : SimplexCategory}
    (s : T.toSSet ⟶ J.obj k) :
    (endpointInclusion T ⊗ₘ 𝟙 I) ≫
        (graphPrism s ≫ (cylinder T).app (K k)) =
      fst JTXiEndpointCollapse.boundary I ≫ (boundary T).app (K k) := by
  rw [← Category.assoc, graphPrism_natural, Category.assoc,
    (isPushout T (K k)).w, ← Category.assoc, graphPrism, lift_fst]

/-- The prism of a graph descends to a map of the actual reduced cylinders. -/
def cylinderMap (T : NecklaceCode) {k : SimplexCategory}
    (s : T.toSSet ⟶ J.obj k) :
    (value T).obj ⦋1⦌ ⟶ (value T).obj (K k) :=
  (isPushout T ⦋1⦌).desc (graphPrism s ≫ (cylinder T).app (K k))
    ((boundary T).app (K k)) (graphPrism_boundary T s)

theorem cylinderMap_cylinder (T : NecklaceCode) {k : SimplexCategory}
    (s : T.toSSet ⟶ J.obj k) :
    (cylinder T).app ⦋1⦌ ≫ cylinderMap T s =
      graphPrism s ≫ (cylinder T).app (K k) :=
  (isPushout T ⦋1⦌).inl_desc _ _ _

theorem cylinderMap_boundary (T : NecklaceCode) {k : SimplexCategory}
    (s : T.toSSet ⟶ J.obj k) :
    (boundary T).app ⦋1⦌ ≫ cylinderMap T s = (boundary T).app (K k) :=
  (isPushout T ⦋1⦌).inr_desc _ _ _

/-- Each time slice of the source cylinder is under its whole boundary. -/
theorem timeSlice_boundary (T : NecklaceCode) (t : Fin 2) :
    endpointInclusion T ≫ (timeSlice T.toSSet t ≫ (cylinder T).app ⦋1⦌) =
      (boundary T).app ⦋1⦌ := by
  have h := timeSlice_natural (endpointInclusion T) t
  rw [← Category.assoc, ← h, Category.assoc, (isPushout T ⦋1⦌).w,
    ← Category.assoc, timeSlice_fst, Category.id_comp]

/-- The full slice of the descended prism is the prescribed enlarged graph. -/
theorem cylinderMap_slice (T : NecklaceCode) {k : SimplexCategory}
    (s : T.toSSet ⟶ J.obj k) (t : Fin 2) :
    (timeSlice T.toSSet t ≫ (cylinder T).app ⦋1⦌) ≫ cylinderMap T s =
      lift (𝟙 T.toSSet) (s ≫ J.map (slice k t)) ≫ (cylinder T).app (K k) := by
  rw [Category.assoc, cylinderMap_cylinder, ← Category.assoc, graphPrism_slice]

end

end DaggerModels.PartII.JTGraphPrismCylinder
