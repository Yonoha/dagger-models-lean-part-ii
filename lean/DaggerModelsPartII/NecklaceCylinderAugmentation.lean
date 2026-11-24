import DaggerModelsPartII.JTNecklaceEndpointCylinder
import DaggerModelsPartII.ReducedGroupoidCylinderAugmentation
import ChosenNecklaceIntervalSingle
import OriginalProductBeadConstantNat

/-!
# The native necklace endpoint-cylinder augmentation

The general reduced groupoid-cylinder augmentation is applied to the original
two endpoints of every native necklace, including the point code. Naturality
uses the augmentation itself; no groupoid-parameter vertex is selected
naturally in the parameter.
-/

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory Simplicial Opposite DaggerModels
open DaggerChosenRigidificationNecklace
open DaggerModels.PartII.JTNecklaceEndpointCylinder
open DaggerModels.PartII.ReducedGroupoidCylinderAugmentation
open DaggerNativeJoyalMappingTest

namespace DaggerModels.PartII.NecklaceCylinderAugmentation

noncomputable section

private abbrev NCode := NecklaceCode
private abbrev J := GroupoidSimplex.parameter

/-- The actual projection from the endpoint-collapsed necklace cylinder. -/
def augmentation (T : NCode) (k : SimplexCategory) :
    (value T).obj k ⟶ T.toSSet :=
  ReducedGroupoidCylinderAugmentation.augmentation (endpointInclusion T) k

/-- The uncollapsed cylinder projects to the same native necklace. -/
theorem augmentation_cylinder (T : NCode) (k : SimplexCategory) :
    (cylinder T).app k ≫ augmentation T k =
      CartesianMonoidalCategory.fst T.toSSet (J.obj k) :=
  ReducedGroupoidCylinderAugmentation.augmentation_cylinder (endpointInclusion T) k

/-- The fixed ordered boundary retains its original endpoint inclusion. -/
theorem augmentation_boundary (T : NCode) (k : SimplexCategory) :
    (boundary T).app k ≫ augmentation T k = endpointInclusion T :=
  ReducedGroupoidCylinderAugmentation.augmentation_boundary (endpointInclusion T) k

/-- The augmentation commutes with every original parameter operator. -/
theorem augmentation_parameter_natural (T : NCode)
    {k l : SimplexCategory} (g : k ⟶ l) :
    (value T).map g ≫ augmentation T l = augmentation T k :=
  ReducedGroupoidCylinderAugmentation.augmentation_natural (endpointInclusion T) g

/-- The augmentation commutes with every native necklace map, including
collapsed-bead maps. -/
theorem augmentation_native_natural {T U : NCode} (f : T ⟶ U)
    (k : SimplexCategory) :
    nativeMap f k ≫ augmentation U k = augmentation T k ≫ f.map := by
  apply (isPushout T k).hom_ext
  · rw [← Category.assoc, nativeMap_cylinder, Category.assoc,
      augmentation_cylinder, ← Category.assoc, augmentation_cylinder]
    exact CartesianMonoidalCategory.tensorHom_fst f.map (𝟙 (J.obj k))
  · rw [← Category.assoc, nativeMap_boundary, augmentation_boundary,
      ← Category.assoc, augmentation_boundary]
    exact (endpointInclusion_natural f).symm

/-- The two distinct native outer vertices give a monomorphic boundary
when the necklace has positive length. -/
theorem endpointInclusion_mono_of_pos (T : NCode) (h : 0 < T.len) :
    Mono (endpointInclusion T) := by
  have hne : (0 : Fin (T.len + 1)) ≠ Fin.last T.len := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_zero, Fin.val_last] at hv
    omega
  have hedge : Mono (DaggerOriginalProductGadget.edgeToAmbient T) := by
    apply (SSet.stdSimplex.mono_iff 1
      (DaggerOriginalProductGadget.edgeToAmbient T)).2
    intro a b he
    apply SSet.stdSimplex.obj₀Equiv.injective
    have hv := congrArg SSet.stdSimplex.obj₀Equiv he
    change DaggerOriginalProductGadget.pairOrderHom T.len 0 (Fin.last T.len)
        (Fin.zero_le _) (SSet.stdSimplex.obj₀Equiv a) =
      DaggerOriginalProductGadget.pairOrderHom T.len 0 (Fin.last T.len)
        (Fin.zero_le _) (SSet.stdSimplex.obj₀Equiv b) at hv
    generalize ha : SSet.stdSimplex.obj₀Equiv a = i at hv ⊢
    generalize hb : SSet.stdSimplex.obj₀Equiv b = j at hv ⊢
    fin_cases i <;> fin_cases j
    · rfl
    · exact False.elim (hne (by simpa [DaggerOriginalProductGadget.pairOrderHom] using hv))
    · exact False.elim (hne (by
        symm
        simpa [DaggerOriginalProductGadget.pairOrderHom] using hv))
    · rfl
  have hδfirst : SSet.stdSimplex.δ (1 : Fin 2) =
      SSet.yonedaEquiv.symm
        (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    rw [SSet.stdSimplex.δ_one]
    rfl
  have hδlast : SSet.stdSimplex.δ (0 : Fin 2) =
      SSet.yonedaEquiv.symm
        (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
    rw [SSet.stdSimplex.δ_zero]
    rfl
  have hfactor : endpointInclusion T ≫ T.inclusion =
      (SSet.boundary 1).ι ≫ DaggerOriginalProductGadget.edgeToAmbient T := by
    apply SSet.boundary₁.hom_ext
    · calc
        SSet.boundary₁.ι₀ ≫ (endpointInclusion T ≫ T.inclusion) =
            (SSet.boundary₁.ι₀ ≫ endpointInclusion T) ≫ T.inclusion :=
          (Category.assoc _ _ _).symm
        _ = SSet.yonedaEquiv.symm T.first ≫ T.inclusion := by
          change SSet.boundary₁.ι₀ ≫ SSet.boundary₁.desc T.first T.last ≫
            T.inclusion = _
          rw [← Category.assoc, SSet.boundary₁.ι₀_desc]
        _ = SSet.yonedaEquiv.symm (T.inclusion.app (op ⦋0⦌) T.first) :=
          SSet.yonedaEquiv_symm_comp _ _
        _ = SSet.boundary₁.ι₀ ≫
              ((SSet.boundary 1).ι ≫
                DaggerOriginalProductGadget.edgeToAmbient T) := by
          rw [DaggerOriginalProductGadget.inclusion_first_std]
          rw [← Category.assoc, SSet.boundary₁.ι₀_ι, hδfirst,
            SSet.yonedaEquiv_symm_comp,
            DaggerOriginalProductGadget.edgeToAmbient_first]
    · calc
        SSet.boundary₁.ι₁ ≫ (endpointInclusion T ≫ T.inclusion) =
            (SSet.boundary₁.ι₁ ≫ endpointInclusion T) ≫ T.inclusion :=
          (Category.assoc _ _ _).symm
        _ = SSet.yonedaEquiv.symm T.last ≫ T.inclusion := by
          change SSet.boundary₁.ι₁ ≫ SSet.boundary₁.desc T.first T.last ≫
            T.inclusion = _
          rw [← Category.assoc, SSet.boundary₁.ι₁_desc]
        _ = SSet.yonedaEquiv.symm (T.inclusion.app (op ⦋0⦌) T.last) :=
          SSet.yonedaEquiv_symm_comp _ _
        _ = SSet.boundary₁.ι₁ ≫
              ((SSet.boundary 1).ι ≫
                DaggerOriginalProductGadget.edgeToAmbient T) := by
          rw [DaggerOriginalProductGadget.inclusion_last_std]
          rw [← Category.assoc, SSet.boundary₁.ι₁_ι, hδlast,
            SSet.yonedaEquiv_symm_comp,
            DaggerOriginalProductGadget.edgeToAmbient_last]
  letI : Mono (DaggerOriginalProductGadget.edgeToAmbient T) := hedge
  haveI : Mono (endpointInclusion T ≫ T.inclusion) := by
    rw [hfactor]
    infer_instance
  exact mono_of_mono (endpointInclusion T) T.inclusion

/-- The point code's boundary is split epimorphic, despite identifying its
two formal endpoints. -/
private def pointSection : (NecklaceCode.point).toSSet ⟶
    JTXiEndpointCollapse.boundary :=
  SSet.boundary₁.ι₀

private theorem pointSection_augmentation :
    pointSection ≫ endpointInclusion NecklaceCode.point =
      𝟙 (NecklaceCode.point).toSSet := by
  exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The original Joyal weak class contains every native necklace-cylinder
augmentation, including the zero-length point code. -/
theorem augmentation_weak (T : NCode) (k : SimplexCategory) :
    weakCategoricalEquivalences (augmentation T k) := by
  by_cases h : T.len = 0
  · have hpoint : T = NecklaceCode.point := NecklaceCode.code_eq_point_of_zero T h
    subst T
    haveI : IsIso (augmentation NecklaceCode.point k) :=
      ReducedGroupoidCylinderAugmentation.augmentation_isIso_of_split_epi
        (endpointInclusion NecklaceCode.point) k pointSection pointSection_augmentation
    exact MorphismProperty.of_isIso weakCategoricalEquivalences _
  · have hpos : 0 < T.len := Nat.pos_of_ne_zero h
    letI : Mono (endpointInclusion T) := endpointInclusion_mono_of_pos T hpos
    exact ReducedGroupoidCylinderAugmentation.augmentation_weak (endpointInclusion T) k

end

end DaggerModels.PartII.NecklaceCylinderAugmentation
