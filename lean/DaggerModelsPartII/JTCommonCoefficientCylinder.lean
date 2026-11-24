import DaggerModelsPartII.JTCommonCoefficientGroupoidPrism
import DaggerModelsPartII.JTHigherGraphPrismCylinder

/-!
# The actual reduced cylinders over a common coefficient
-/

set_option autoImplicit false

open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTCommonCoefficientParameter

open JTHigherInterleavedParameter (common)
open JTHigherGroupoidParameterPrism (timeSlice timeSlice_natural)
open JTNecklaceEndpointCylinder JTParameterContraction

noncomputable section

private abbrev J := GroupoidSimplex.parameter

/-- Keep the actual necklace coordinate while pairing its label with time. -/
def graphPrism {X : SSet.{0}} {k b : SimplexCategory}
    (c : k ⟶ b) (s : X ⟶ J.obj k) (n : SimplexCategory) :
    X ⊗ J.obj n ⟶ X ⊗ J.obj (common k n) :=
  lift (fst X (J.obj n)) ((s ⊗ₘ 𝟙 (J.obj n)) ≫ paired c n)

theorem graphPrism_natural {X Y : SSet.{0}} {k b : SimplexCategory}
    (c : k ⟶ b) (f : X ⟶ Y) (s : Y ⟶ J.obj k) (n : SimplexCategory) :
    (f ⊗ₘ 𝟙 (J.obj n)) ≫ graphPrism c s n =
      graphPrism c (f ≫ s) n ≫ (f ⊗ₘ 𝟙 (J.obj (common k n))) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [graphPrism, Category.assoc, tensorHom_fst, lift_fst, lift_fst_assoc]
  · simp only [graphPrism, Category.assoc, tensorHom_snd, lift_snd, Category.comp_id]
    rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]

theorem graphPrism_slice {X : SSet.{0}} {k b : SimplexCategory}
    (c : k ⟶ b) (s : X ⟶ J.obj k) (n : SimplexCategory) (t : Fin (n.len + 1)) :
    timeSlice X n t ≫ graphPrism c s n =
      lift (𝟙 X) (s ≫ J.map (slice c n t)) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [timeSlice, graphPrism, Category.assoc, lift_fst]
  · simp only [Category.assoc, graphPrism, lift_snd]
    rw [← Category.assoc, timeSlice_natural, Category.assoc, paired_slice]

theorem graphPrism_base {X : SSet.{0}} {k b : SimplexCategory}
    (c : k ⟶ b) (s : X ⟶ J.obj k) (n : SimplexCategory) :
    graphPrism c s n ≫ (𝟙 X ⊗ₘ J.map (base c n)) =
      fst X (J.obj n) ≫ lift (𝟙 X) (s ≫ J.map c) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [graphPrism, Category.assoc, tensorHom_fst, lift_fst, Category.comp_id]
  · simp only [graphPrism, Category.assoc, tensorHom_snd, lift_snd, lift_snd_assoc]
    rw [paired_base, tensorHom_fst_assoc]

theorem graphPrism_constant {X : SSet.{0}} {k b : SimplexCategory}
    (c : k ⟶ b) (n : SimplexCategory) (a : Fin (k.len + 1)) :
    graphPrism c (SSet.stdSimplex.isTerminalObj₀.from X ≫ parameterVertex k a) n =
      𝟙 X ⊗ₘ J.map (vertical c n a) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [graphPrism, lift_fst, tensorHom_fst, Category.comp_id]
  · simp only [graphPrism, lift_snd, tensorHom_snd]
    rw [← Category.id_comp (𝟙 (J.obj n)), ← tensorHom_comp_tensorHom, Category.assoc,
      paired_vertex, ← Category.assoc, tensorHom_snd, Category.comp_id]

/-- Natural comparison of entire groupoid prisms in both variables. -/
theorem graphPrism_map {X : SSet.{0}} {k l b n m : SimplexCategory}
    {c : k ⟶ b} {d : l ⟶ b} (f : k ⟶ l) (hf : f ≫ d = c)
    (j : n ⟶ m) (hj : Function.Injective j.toOrderHom)
    (s : X ⟶ J.obj k) (s' : X ⟶ J.obj l) (hs : s ≫ J.map f = s') :
    graphPrism c s n ≫ (X ◁ J.map (map f hf j hj)) =
      (X ◁ J.map j) ≫ graphPrism d s' m := by
  simp only [← MonoidalCategory.id_tensorHom]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [graphPrism, Category.assoc, tensorHom_fst, lift_fst, Category.comp_id]
  · calc
      _ = (s ⊗ₘ 𝟙 (J.obj n)) ≫ paired c n ≫ J.map (map f hf j hj) := by
        rw [Category.assoc, tensorHom_snd, ← Category.assoc, graphPrism, lift_snd,
          Category.assoc]
      _ = ((𝟙 X ⊗ₘ J.map j) ≫ (s' ⊗ₘ 𝟙 (J.obj m))) ≫ paired d m := by
        rw [paired_map, ← Category.assoc, tensorHom_comp_tensorHom,
          tensorHom_comp_tensorHom, hs, Category.id_comp, Category.id_comp, Category.comp_id]
      _ = _ := by rw [Category.assoc, Category.assoc, graphPrism, lift_snd]

private theorem graphPrism_boundary (T : NecklaceCode) {k b : SimplexCategory}
    (c : k ⟶ b) (s : T.toSSet ⟶ J.obj k) (n : SimplexCategory) :
    (endpointInclusion T ⊗ₘ 𝟙 (J.obj n)) ≫
        (graphPrism c s n ≫ (cylinder T).app (common k n)) =
      fst JTXiEndpointCollapse.boundary (J.obj n) ≫ (boundary T).app (common k n) := by
  rw [← Category.assoc, graphPrism_natural, Category.assoc,
    (isPushout T (common k n)).w, ← Category.assoc, graphPrism, lift_fst]

/-- The map between the original reduced cylinders with both ends collapsed. -/
def cylinderMap (T : NecklaceCode) {k b : SimplexCategory}
    (c : k ⟶ b) (s : T.toSSet ⟶ J.obj k) (n : SimplexCategory) :
    (value T).obj n ⟶ (value T).obj (common k n) :=
  (isPushout T n).desc (graphPrism c s n ≫ (cylinder T).app (common k n))
    ((boundary T).app (common k n)) (graphPrism_boundary T c s n)

theorem cylinderMap_cylinder (T : NecklaceCode) {k b : SimplexCategory}
    (c : k ⟶ b) (s : T.toSSet ⟶ J.obj k) (n : SimplexCategory) :
    (cylinder T).app n ≫ cylinderMap T c s n =
      graphPrism c s n ≫ (cylinder T).app (common k n) :=
  (isPushout T n).inl_desc _ _ _

theorem cylinderMap_boundary (T : NecklaceCode) {k b : SimplexCategory}
    (c : k ⟶ b) (s : T.toSSet ⟶ J.obj k) (n : SimplexCategory) :
    (boundary T).app n ≫ cylinderMap T c s n = (boundary T).app (common k n) :=
  (isPushout T n).inr_desc _ _ _

/-- Naturality on the whole original reduced cylinder, including both
ordered endpoints. -/
theorem cylinderMap_map (T : NecklaceCode) {k l b n m : SimplexCategory}
    {c : k ⟶ b} {d : l ⟶ b} (f : k ⟶ l) (hf : f ≫ d = c)
    (j : n ⟶ m) (hj : Function.Injective j.toOrderHom)
    (s : T.toSSet ⟶ J.obj k) (s' : T.toSSet ⟶ J.obj l) (hs : s ≫ J.map f = s') :
    cylinderMap T c s n ≫ (value T).map (map f hf j hj) =
      (value T).map j ≫ cylinderMap T d s' m := by
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
      ← Category.assoc, graphPrism_map f hf j hj s s' hs, Category.assoc,
      ← Category.assoc ((cylinder T).app n), ← hC, Category.assoc,
      cylinderMap_cylinder]
  · rw [← Category.assoc, cylinderMap_boundary, hB,
      ← Category.assoc, hB, cylinderMap_boundary]

end

end DaggerModels.PartII.JTCommonCoefficientParameter
