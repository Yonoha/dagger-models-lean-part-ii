import DaggerModelsPartII.JTChangingCoefficientBridgeGroupoid
import DaggerModelsPartII.JTCommonCoefficientCylinder

/-!
# The joining map on the original reduced cylinders
-/

set_option autoImplicit false

open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTChangingCoefficientBridgeCylinder

open JTChangingCoefficientBridgeOrder JTChangingCoefficientBridgeTime
open JTChangingCoefficientBridgeGroupoid JTNecklaceEndpointCylinder
open JTChangingCoefficientBridgePrism JTParameterContraction
open JTHigherGroupoidParameterPrism (timeSlice timeSlice_natural)

noncomputable section

private abbrev J := GroupoidSimplex.parameter

variable {k b b' : SimplexCategory} (c : k ⟶ b) (h : b ⟶ b') (n : SimplexCategory)

/-- The actual necklace coordinate remains fixed along the joining prism. -/
def graphPrism {X : SSet.{0}} (s : X ⟶ J.obj k) :
    X ⊗ J.obj (time n) ⟶ X ⊗ J.obj (bridge k n) :=
  lift (fst X (J.obj (time n))) ((s ⊗ₘ 𝟙 (J.obj (time n))) ≫ paired c h n)

theorem graphPrism_natural {X Y : SSet.{0}} (f : X ⟶ Y) (s : Y ⟶ J.obj k) :
    (f ⊗ₘ 𝟙 (J.obj (time n))) ≫ graphPrism c h n s =
      graphPrism c h n (f ≫ s) ≫ (f ⊗ₘ 𝟙 (J.obj (bridge k n))) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [graphPrism, Category.assoc, tensorHom_fst, lift_fst, lift_fst_assoc]
  · simp only [graphPrism, Category.assoc, tensorHom_snd, lift_snd, Category.comp_id]
    rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]

theorem graphPrism_base {X : SSet.{0}} (s : X ⟶ J.obj k) :
    graphPrism c h n s ≫ (𝟙 X ⊗ₘ J.map (base c h n)) =
      fst X (J.obj (time n)) ≫ lift (𝟙 X) (s ≫ J.map (c ≫ h)) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [graphPrism, Category.assoc, tensorHom_fst, lift_fst, Category.comp_id]
  · simp only [graphPrism, Category.assoc, tensorHom_snd, lift_snd, lift_snd_assoc]
    rw [paired_base, tensorHom_fst_assoc]

theorem graphPrism_constant {X : SSet.{0}} (a : Fin (k.len + 1)) :
    graphPrism c h n (SSet.stdSimplex.isTerminalObj₀.from X ≫ parameterVertex k a) =
      𝟙 X ⊗ₘ J.map (vertical c h n a) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [graphPrism, lift_fst, tensorHom_fst, Category.comp_id]
  · simp only [graphPrism, lift_snd, tensorHom_snd]
    rw [← Category.id_comp (𝟙 (J.obj (time n))), ← tensorHom_comp_tensorHom,
      Category.assoc, paired_vertex, ← Category.assoc, tensorHom_snd, Category.comp_id]

theorem graphPrism_slice {X : SSet.{0}} (s : X ⟶ J.obj k) (t : Fin ((time n).len + 1)) :
    timeSlice X (time n) t ≫ graphPrism c h n s =
      lift (𝟙 X) (s ≫ J.map (slice c h n t)) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [timeSlice, graphPrism, Category.assoc, lift_fst]
  · simp only [Category.assoc, graphPrism, lift_snd]
    rw [← Category.assoc, timeSlice_natural, Category.assoc, paired_slice]

/-- The existing full common-coefficient graph prism at each side. -/
abbrev sideGraphPrism {X : SSet.{0}} (s : X ⟶ J.obj k) (e : Fin 2) :
    X ⊗ J.obj n ⟶ X ⊗ J.obj (JTHigherInterleavedParameter.common k n) :=
  if e = 0 then JTCommonCoefficientParameter.graphPrism c s n
  else JTCommonCoefficientParameter.graphPrism (c ≫ h) s n

theorem graphPrism_side {X : SSet.{0}} (s : X ⟶ J.obj k) (e : Fin 2) :
    (X ◁ J.map (timeSide n e)) ≫ graphPrism c h n s =
      sideGraphPrism c h n s e ≫ (X ◁ J.map (side c h n e)) := by
  have hs : sideGraphPrism c h n s e =
      lift (fst X (J.obj n)) ((s ⊗ₘ 𝟙 (J.obj n)) ≫ sidePaired c h n e) := by
    by_cases he : e = 0 <;>
      simp only [sideGraphPrism, sidePaired, he, if_true, if_false,
        JTCommonCoefficientParameter.graphPrism]
  rw [hs]
  simp only [← MonoidalCategory.id_tensorHom]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [graphPrism, Category.assoc, tensorHom_fst, lift_fst, Category.comp_id]
  · simp only [graphPrism, Category.assoc, tensorHom_snd, lift_snd, lift_snd_assoc]
    rw [← paired_side,
      ← MonoidalCategory.id_tensorHom, ← Category.assoc (s ⊗ₘ 𝟙 (J.obj n)),
      ← Category.assoc (𝟙 X ⊗ₘ J.map (timeSide n e)), tensorHom_comp_tensorHom,
      tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id, Category.comp_id]
    rfl

private theorem graphPrism_boundary (T : NecklaceCode) (s : T.toSSet ⟶ J.obj k) :
    (endpointInclusion T ⊗ₘ 𝟙 (J.obj (time n))) ≫
        (graphPrism c h n s ≫ (cylinder T).app (bridge k n)) =
      fst JTXiEndpointCollapse.boundary (J.obj (time n)) ≫ (boundary T).app (bridge k n) := by
  rw [← Category.assoc, graphPrism_natural, Category.assoc,
    (isPushout T (bridge k n)).w, ← Category.assoc, graphPrism, lift_fst]

/-- The joining map preserves both endpoints in the actual reduced cylinder. -/
def cylinderMap (T : NecklaceCode) (s : T.toSSet ⟶ J.obj k) :
    (value T).obj (time n) ⟶ (value T).obj (bridge k n) :=
  (isPushout T (time n)).desc (graphPrism c h n s ≫ (cylinder T).app (bridge k n))
    ((boundary T).app (bridge k n)) (graphPrism_boundary c h n T s)

theorem cylinderMap_cylinder (T : NecklaceCode) (s : T.toSSet ⟶ J.obj k) :
    (cylinder T).app (time n) ≫ cylinderMap c h n T s =
      graphPrism c h n s ≫ (cylinder T).app (bridge k n) :=
  (isPushout T (time n)).inl_desc _ _ _

theorem cylinderMap_boundary (T : NecklaceCode) (s : T.toSSet ⟶ J.obj k) :
    (boundary T).app (time n) ≫ cylinderMap c h n T s = (boundary T).app (bridge k n) :=
  (isPushout T (time n)).inr_desc _ _ _

/-- Each side uses its original common-coefficient reduced cylinder. -/
abbrev sideCylinderMap (T : NecklaceCode) (s : T.toSSet ⟶ J.obj k) (e : Fin 2) :
    (value T).obj n ⟶ (value T).obj (JTHigherInterleavedParameter.common k n) :=
  if e = 0 then JTCommonCoefficientParameter.cylinderMap T c s n
  else JTCommonCoefficientParameter.cylinderMap T (c ≫ h) s n

theorem cylinderMap_side (T : NecklaceCode) (s : T.toSSet ⟶ J.obj k) (e : Fin 2) :
    (value T).map (timeSide n e) ≫ cylinderMap c h n T s =
      sideCylinderMap c h n T s e ≫ (value T).map (side c h n e) := by
  have hC {a a' : SimplexCategory} (g : a ⟶ a') :
      (T.toSSet ◁ J.map g) ≫ (cylinder T).app a' =
        (cylinder T).app a ≫ (value T).map g :=
    (cylinder T).naturality g
  have hB {a a' : SimplexCategory} (g : a ⟶ a') :
      (boundary T).app a ≫ (value T).map g = (boundary T).app a' := by
    rw [← (boundary T).naturality g]
    exact Category.id_comp _
  have hSC : (cylinder T).app n ≫ sideCylinderMap c h n T s e =
      sideGraphPrism c h n s e ≫ (cylinder T).app (JTHigherInterleavedParameter.common k n) := by
    by_cases he : e = 0 <;>
      simp only [sideCylinderMap, sideGraphPrism, he, if_true, if_false,
        JTCommonCoefficientParameter.cylinderMap_cylinder]
  have hSB : (boundary T).app n ≫ sideCylinderMap c h n T s e =
      (boundary T).app (JTHigherInterleavedParameter.common k n) := by
    by_cases he : e = 0 <;>
      simp only [sideCylinderMap, he, if_true, if_false,
        JTCommonCoefficientParameter.cylinderMap_boundary]
  apply (isPushout T n).hom_ext
  · rw [← Category.assoc, ← hC, Category.assoc, cylinderMap_cylinder,
      ← Category.assoc, graphPrism_side, Category.assoc, hC, ← Category.assoc, ← hSC,
      Category.assoc]
  · rw [← Category.assoc, hB, cylinderMap_boundary, ← Category.assoc, hSB, hB]

end

end DaggerModels.PartII.JTChangingCoefficientBridgeCylinder
