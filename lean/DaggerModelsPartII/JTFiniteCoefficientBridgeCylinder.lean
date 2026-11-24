import DaggerModelsPartII.JTFiniteCoefficientBridgeGroupoid
import DaggerModelsPartII.JTCommonCoefficientCylinder

/-!
# The finite joining map on the original reduced cylinders
-/

set_option autoImplicit false

open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTFiniteCoefficientBridgeCylinder

open JTFiniteCoefficientBridgeOrder JTFiniteCoefficientBridgeTime
open JTFiniteCoefficientBridgeGroupoid JTNecklaceEndpointCylinder
open JTFiniteCoefficientBridgePrism JTParameterContraction
open JTHigherGroupoidParameterPrism (timeSlice timeSlice_natural)

noncomputable section

private abbrev J := GroupoidSimplex.parameter

variable {m : ℕ} {k b' : SimplexCategory} {b : Fin (m + 1) → SimplexCategory}
variable (c : ∀ e, k ⟶ b e) (u : k ⟶ b') (n : SimplexCategory)

/-- The actual necklace coordinate remains fixed along the joining prism. -/
def graphPrism {X : SSet.{0}} (s : X ⟶ J.obj k) :
    X ⊗ J.obj (time m n) ⟶ X ⊗ J.obj (bridge k n m) :=
  lift (fst X (J.obj (time m n))) ((s ⊗ₘ 𝟙 (J.obj (time m n))) ≫ paired c u n)

theorem graphPrism_natural {X Y : SSet.{0}} (f : X ⟶ Y) (s : Y ⟶ J.obj k) :
    (f ⊗ₘ 𝟙 (J.obj (time m n))) ≫ graphPrism c u n s =
      graphPrism c u n (f ≫ s) ≫ (f ⊗ₘ 𝟙 (J.obj (bridge k n m))) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [graphPrism, Category.assoc, tensorHom_fst, lift_fst, lift_fst_assoc]
  · simp only [graphPrism, Category.assoc, tensorHom_snd, lift_snd, Category.comp_id]
    rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]

theorem graphPrism_base {X : SSet.{0}} (s : X ⟶ J.obj k) :
    graphPrism c u n s ≫ (𝟙 X ⊗ₘ J.map (base c u n)) =
      fst X (J.obj (time m n)) ≫ lift (𝟙 X) (s ≫ J.map u) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [graphPrism, Category.assoc, tensorHom_fst, lift_fst, Category.comp_id]
  · simp only [graphPrism, Category.assoc, tensorHom_snd, lift_snd, lift_snd_assoc]
    rw [paired_base, tensorHom_fst_assoc]

theorem graphPrism_constant {X : SSet.{0}} (a : Fin (k.len + 1)) :
    graphPrism c u n (SSet.stdSimplex.isTerminalObj₀.from X ≫ parameterVertex k a) =
      𝟙 X ⊗ₘ J.map (vertical c u n a) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [graphPrism, lift_fst, tensorHom_fst, Category.comp_id]
  · simp only [graphPrism, lift_snd, tensorHom_snd]
    rw [← Category.id_comp (𝟙 (J.obj (time m n))), ← tensorHom_comp_tensorHom,
      Category.assoc, paired_vertex, ← Category.assoc, tensorHom_snd, Category.comp_id]

theorem graphPrism_slice {X : SSet.{0}} (s : X ⟶ J.obj k) (t : Fin ((time m n).len + 1)) :
    timeSlice X (time m n) t ≫ graphPrism c u n s =
      lift (𝟙 X) (s ≫ J.map (slice c u n t)) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [timeSlice, graphPrism, Category.assoc, lift_fst]
  · simp only [Category.assoc, graphPrism, lift_snd]
    rw [← Category.assoc, timeSlice_natural, Category.assoc, paired_slice]

variable (h : ∀ e, b e ⟶ b') (hu : ∀ e, c e ≫ h e = u)

theorem graphPrism_side {X : SSet.{0}} (s : X ⟶ J.obj k) (e : Fin (m + 1)) :
    (X ◁ J.map (timeSide n e)) ≫ graphPrism c u n s =
      JTCommonCoefficientParameter.graphPrism (c e) s n ≫ (X ◁ J.map (side c u h hu n e)) := by
  simp only [← MonoidalCategory.id_tensorHom]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [graphPrism, JTCommonCoefficientParameter.graphPrism,
      Category.assoc, tensorHom_fst, lift_fst, Category.comp_id]
  · simp only [graphPrism, JTCommonCoefficientParameter.graphPrism,
      Category.assoc, tensorHom_snd, lift_snd, lift_snd_assoc]
    rw [← paired_side c u n h hu e, ← MonoidalCategory.id_tensorHom,
      ← Category.assoc (s ⊗ₘ 𝟙 (J.obj n)),
      ← Category.assoc (𝟙 X ⊗ₘ J.map (timeSide n e)), tensorHom_comp_tensorHom,
      tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id, Category.comp_id]
    rfl

private theorem graphPrism_boundary (T : NecklaceCode) (s : T.toSSet ⟶ J.obj k) :
    (endpointInclusion T ⊗ₘ 𝟙 (J.obj (time m n))) ≫
        (graphPrism c u n s ≫ (cylinder T).app (bridge k n m)) =
      fst JTXiEndpointCollapse.boundary (J.obj (time m n)) ≫ (boundary T).app (bridge k n m) := by
  rw [← Category.assoc, graphPrism_natural, Category.assoc,
    (isPushout T (bridge k n m)).w, ← Category.assoc, graphPrism, lift_fst]

/-- The joining map preserves both endpoints in the actual reduced cylinder. -/
def cylinderMap (T : NecklaceCode) (s : T.toSSet ⟶ J.obj k) :
    (value T).obj (time m n) ⟶ (value T).obj (bridge k n m) :=
  (isPushout T (time m n)).desc (graphPrism c u n s ≫ (cylinder T).app (bridge k n m))
    ((boundary T).app (bridge k n m)) (graphPrism_boundary c u n T s)

theorem cylinderMap_cylinder (T : NecklaceCode) (s : T.toSSet ⟶ J.obj k) :
    (cylinder T).app (time m n) ≫ cylinderMap c u n T s =
      graphPrism c u n s ≫ (cylinder T).app (bridge k n m) :=
  (isPushout T (time m n)).inl_desc _ _ _

theorem cylinderMap_boundary (T : NecklaceCode) (s : T.toSSet ⟶ J.obj k) :
    (boundary T).app (time m n) ≫ cylinderMap c u n T s = (boundary T).app (bridge k n m) :=
  (isPushout T (time m n)).inr_desc _ _ _

/-- Restriction to any entire time face is the original reduced cylinder map. -/
theorem cylinderMap_side (T : NecklaceCode) (s : T.toSSet ⟶ J.obj k) (e : Fin (m + 1)) :
    (value T).map (timeSide n e) ≫ cylinderMap c u n T s =
      JTCommonCoefficientParameter.cylinderMap T (c e) s n ≫ (value T).map (side c u h hu n e) := by
  have hC {a a' : SimplexCategory} (g : a ⟶ a') :
      (T.toSSet ◁ J.map g) ≫ (cylinder T).app a' =
        (cylinder T).app a ≫ (value T).map g :=
    (cylinder T).naturality g
  have hB {a a' : SimplexCategory} (g : a ⟶ a') :
      (boundary T).app a ≫ (value T).map g = (boundary T).app a' := by
    rw [← (boundary T).naturality g]
    exact Category.id_comp _
  apply (isPushout T n).hom_ext
  · rw [← Category.assoc, ← hC, Category.assoc, cylinderMap_cylinder,
      ← Category.assoc, graphPrism_side c u n h hu s e, Category.assoc, hC,
      ← Category.assoc ((cylinder T).app n),
      JTCommonCoefficientParameter.cylinderMap_cylinder, Category.assoc]
  · rw [← Category.assoc, hB, cylinderMap_boundary, ← Category.assoc,
      JTCommonCoefficientParameter.cylinderMap_boundary, hB]

end

end DaggerModels.PartII.JTFiniteCoefficientBridgeCylinder
