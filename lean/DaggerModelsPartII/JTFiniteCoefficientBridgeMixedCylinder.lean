import DaggerModelsPartII.JTFiniteCoefficientBridgeCylinder

/-!
# Mixed naturality of finite coefficient bridge cylinders
-/

set_option autoImplicit false

open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTFiniteCoefficientBridgeMixedCylinder

open JTFiniteCoefficientBridgeOrder (bridge)
open JTFiniteCoefficientBridgeTime (time)
open JTFiniteCoefficientBridgeGroupoid (paired)
open JTFiniteCoefficientBridgeCylinder (graphPrism cylinderMap cylinderMap_cylinder
  cylinderMap_boundary)
open JTNecklaceEndpointCylinder

noncomputable section

private abbrev J := GroupoidSimplex.parameter

variable {m m' : ℕ} {k l b' d' : SimplexCategory}
variable {b : Fin (m + 1) → SimplexCategory}
variable {d : Fin (m' + 1) → SimplexCategory}
variable (c : ∀ e, k ⟶ b e) (u : k ⟶ b') (n : SimplexCategory)
variable (c' : ∀ e, l ⟶ d e) (u' : l ⟶ d') (n' : SimplexCategory)
variable {S T : NecklaceCode} (v : S ⟶ T) (f : k ⟶ l)
variable (s : S.toSSet ⟶ J.obj k) (t : T.toSSet ⟶ J.obj l)
variable (hs : s ≫ J.map f = v.map ≫ t)
variable (j : time m n ⟶ time m' n') (a : bridge k n m ⟶ bridge l n' m')
variable (hp : paired c u n ≫ J.map a =
  (J.map f ⊗ₘ J.map j) ≫ paired c' u' n')

include f hs hp

/-- The uncollapsed graph prisms respect a mixed pairing square. -/
theorem graphPrism_mixed :
    graphPrism c u n s ≫ (v.map ⊗ₘ J.map a) =
      (v.map ⊗ₘ J.map j) ≫ graphPrism c' u' n' t := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [graphPrism, Category.assoc, tensorHom_fst, lift_fst, lift_fst_assoc]
  · simp only [graphPrism, Category.assoc, tensorHom_snd, lift_snd, lift_snd_assoc]
    rw [hp, ← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
    have h : ((s ≫ J.map f) ⊗ₘ J.map j) =
        (v.map ⊗ₘ J.map j) ≫ (t ⊗ₘ 𝟙 (J.obj (time m' n'))) := by
      rw [hs, tensorHom_comp_tensorHom, Category.comp_id]
    rw [h, Category.assoc]

/-- Mixed naturality of the actual reduced cylinders, including the ordered endpoints. -/
theorem cylinderMap_mixed :
    cylinderMap c u n S s ≫ (value S).map a ≫ nativeMap v (bridge l n' m') =
      (value S).map j ≫ nativeMap v (time m' n') ≫ cylinderMap c' u' n' T t := by
  have hC {Q : NecklaceCode} {x y : SimplexCategory} (g : x ⟶ y) :
      (Q.toSSet ◁ J.map g) ≫ (cylinder Q).app y =
        (cylinder Q).app x ≫ (value Q).map g :=
    (cylinder Q).naturality g
  have hB {Q : NecklaceCode} {x y : SimplexCategory} (g : x ⟶ y) :
      (boundary Q).app x ≫ (value Q).map g = (boundary Q).app y := by
    rw [← (boundary Q).naturality g]
    exact Category.id_comp _
  have hTensorBridge :
      (S.toSSet ◁ J.map a) ≫
        (v.map ⊗ₘ 𝟙 (J.obj (bridge l n' m'))) = v.map ⊗ₘ J.map a := by
    change (𝟙 S.toSSet ⊗ₘ J.map a) ≫
      (v.map ⊗ₘ 𝟙 (J.obj (bridge l n' m'))) = _
    rw [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  have hTensorTime :
      (S.toSSet ◁ J.map j) ≫
        (v.map ⊗ₘ 𝟙 (J.obj (time m' n'))) = v.map ⊗ₘ J.map j := by
    change (𝟙 S.toSSet ⊗ₘ J.map j) ≫
      (v.map ⊗ₘ 𝟙 (J.obj (time m' n'))) = _
    rw [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  apply (isPushout S (time m n)).hom_ext
  · rw [← Category.assoc, cylinderMap_cylinder]
    calc
      _ = graphPrism c u n s ≫ (S.toSSet ◁ J.map a) ≫
          (cylinder S).app (bridge l n' m') ≫ nativeMap v (bridge l n' m') := by
        simpa only [Category.assoc] using congrArg
          (fun h ↦ graphPrism c u n s ≫ h ≫ nativeMap v (bridge l n' m')) (hC a).symm
      _ = graphPrism c u n s ≫ (S.toSSet ◁ J.map a) ≫
          (v.map ⊗ₘ 𝟙 (J.obj (bridge l n' m'))) ≫
          (cylinder T).app (bridge l n' m') := by
        simpa only [Category.assoc] using congrArg
          (fun h ↦ graphPrism c u n s ≫ (S.toSSet ◁ J.map a) ≫ h)
          (nativeMap_cylinder v (bridge l n' m'))
      _ = graphPrism c u n s ≫ (v.map ⊗ₘ J.map a) ≫
          (cylinder T).app (bridge l n' m') := by
        simpa only [Category.assoc] using congrArg
          (fun h ↦ graphPrism c u n s ≫ h ≫ (cylinder T).app (bridge l n' m'))
          hTensorBridge
      _ = (v.map ⊗ₘ J.map j) ≫ graphPrism c' u' n' t ≫
          (cylinder T).app (bridge l n' m') := by
        simpa only [Category.assoc] using congrArg
          (fun h ↦ h ≫ (cylinder T).app (bridge l n' m'))
          (graphPrism_mixed c u n c' u' n' v f s t hs j a hp)
      _ = (v.map ⊗ₘ J.map j) ≫ (cylinder T).app (time m' n') ≫
          cylinderMap c' u' n' T t := by
        simpa only [Category.assoc] using congrArg
          (fun h ↦ (v.map ⊗ₘ J.map j) ≫ h)
          (cylinderMap_cylinder c' u' n' T t).symm
      _ = (S.toSSet ◁ J.map j) ≫
          (v.map ⊗ₘ 𝟙 (J.obj (time m' n'))) ≫
          (cylinder T).app (time m' n') ≫ cylinderMap c' u' n' T t := by
        simpa only [Category.assoc] using congrArg
          (fun h ↦ h ≫ (cylinder T).app (time m' n') ≫ cylinderMap c' u' n' T t)
          hTensorTime.symm
      _ = (S.toSSet ◁ J.map j) ≫ (cylinder S).app (time m' n') ≫
          nativeMap v (time m' n') ≫ cylinderMap c' u' n' T t := by
        simpa only [Category.assoc] using congrArg
          (fun h ↦ (S.toSSet ◁ J.map j) ≫ h ≫ cylinderMap c' u' n' T t)
          (nativeMap_cylinder v (time m' n')).symm
      _ = (cylinder S).app (time m n) ≫ (value S).map j ≫
          nativeMap v (time m' n') ≫ cylinderMap c' u' n' T t := by
        simpa only [Category.assoc] using congrArg
          (fun h ↦ h ≫ nativeMap v (time m' n') ≫ cylinderMap c' u' n' T t) (hC j)
  · rw [← Category.assoc, cylinderMap_boundary]
    calc
      _ = (boundary S).app (bridge l n' m') ≫
          nativeMap v (bridge l n' m') := by rw [← Category.assoc, hB a]
      _ = (boundary T).app (bridge l n' m') := nativeMap_boundary v _
      _ = (boundary T).app (time m' n') ≫ cylinderMap c' u' n' T t := by
        exact (cylinderMap_boundary c' u' n' T t).symm
      _ = (boundary S).app (time m' n') ≫ nativeMap v (time m' n') ≫
          cylinderMap c' u' n' T t := by
        simpa only [Category.assoc] using congrArg
          (fun h ↦ h ≫ cylinderMap c' u' n' T t)
          (nativeMap_boundary v (time m' n')).symm
      _ = (boundary S).app (time m n) ≫ (value S).map j ≫
          nativeMap v (time m' n') ≫ cylinderMap c' u' n' T t := by
        simpa only [Category.assoc] using congrArg
          (fun h ↦ h ≫ nativeMap v (time m' n') ≫ cylinderMap c' u' n' T t) (hB j).symm

end

end DaggerModels.PartII.JTFiniteCoefficientBridgeMixedCylinder
