import DaggerModelsPartII.JTRawUnitCylinderCalibration

/-! The exact one-edge cylinder-to-CE comparison is a natural isomorphism. -/

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory Simplicial
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTSingleCylinderCEIso

open JTNecklaceEndpointCylinder JTRawUnitCylinderCalibration

noncomputable section

private abbrev T := single 1
private abbrev J (k : SimplexCategory) := GroupoidSimplex.parameter.obj k
private def tensorIso (k : SimplexCategory) :=
  (singleIso 1) ⊗ᵢ Iso.refl (J k)

private theorem component_isIso (k : SimplexCategory) : IsIso (singleCylinderToCE k) := by
  have hCE := (IsPushout.of_hasPushout JTXiEndpointCollapse.cylinderInclusion JTXiEndpointCollapse.cylinderProjection).map
    ((evaluation SimplexCategory SSet.{0}).obj k)
  have hi : (endpointInclusion T ⊗ₘ 𝟙 (J k)) ≫ (tensorIso k).hom =
      JTXiEndpointCollapse.cylinderInclusion.app k := by
    change (endpointInclusion T ⊗ₘ 𝟙 (J k)) ≫
      ((singleIso 1).hom ⊗ₘ 𝟙 (J k)) = (JTCylinderFrame.j ⊗ₘ 𝟙 (J k))
    rw [tensorHom_comp_tensorHom, Category.id_comp, singleBoundary_to_interval]
  have hC : IsPushout ((endpointInclusion T ⊗ₘ 𝟙 (J k)) ≫ (tensorIso k).hom)
      (JTXiEndpointCollapse.cylinderProjection.app k) (JTXiEndpointCollapse.CE_interval.app k)
      ((boundary T).app k ≫ singleCylinderToCE k) := by
    rw [hi, singleCylinderToCE_boundary]
    exact hCE
  have hw : (tensorIso k).hom ≫ JTXiEndpointCollapse.CE_interval.app k =
      (cylinder T).app k ≫ singleCylinderToCE k :=
    (singleCylinderToCE_cylinder k).symm
  exact (hC.of_left hw (isPushout T k)).isIso_inr_of_isIso

private theorem component_naturality {k l : SimplexCategory} (f : k ⟶ l) :
    (value T).map f ≫ singleCylinderToCE l = singleCylinderToCE k ≫ JTXiEndpointCollapse.CE.map f := by
  apply (isPushout T k).hom_ext
  · have h₁ := (cylinder T).naturality f
    have h₂ := JTXiEndpointCollapse.CE_interval.naturality f
    change (𝟙 T.toSSet ⊗ₘ GroupoidSimplex.parameter.map f) ≫ (cylinder T).app l =
      (cylinder T).app k ≫ (value T).map f at h₁
    change (𝟙 JTXiEndpointCollapse.interval ⊗ₘ GroupoidSimplex.parameter.map f) ≫
        JTXiEndpointCollapse.CE_interval.app l = JTXiEndpointCollapse.CE_interval.app k ≫ JTXiEndpointCollapse.CE.map f at h₂
    rw [← Category.assoc, ← h₁, Category.assoc, singleCylinderToCE_cylinder,
      ← Category.assoc, ← Category.assoc, singleCylinderToCE_cylinder]
    simp only [Category.assoc, ← h₂]
    simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
    exact congrArg
      (fun e : T.toSSet ⟶ JTXiEndpointCollapse.interval ↦
        (e ⊗ₘ GroupoidSimplex.parameter.map f) ≫ JTXiEndpointCollapse.CE_interval.app l)
      (Category.comp_id ((singleIso 1).hom)).symm
  · have h₁ : (boundary T).app k ≫ (value T).map f = (boundary T).app l := by
      simpa only [Functor.const_obj_map, Category.id_comp] using
        ((boundary T).naturality f).symm
    have h₂ : JTXiEndpointCollapse.CE_boundary.app k ≫ JTXiEndpointCollapse.CE.map f = JTXiEndpointCollapse.CE_boundary.app l := by
      simpa only [Functor.const_obj_map, Category.id_comp] using
        (JTXiEndpointCollapse.CE_boundary.naturality f).symm
    rw [← Category.assoc, h₁, singleCylinderToCE_boundary,
      ← Category.assoc, singleCylinderToCE_boundary, h₂]

/-- The same map used in the raw evaluation is an isomorphism of the full
cosimplicial frames under the original boundary. -/
def comparison : under T ≅ Under.lift JTXiEndpointCollapse.CE JTXiEndpointCollapse.CE_boundary :=
  NatIso.ofComponents (fun k ↦ by
    letI := component_isIso k
    exact Under.isoMk (asIso (singleCylinderToCE k)) (singleCylinderToCE_boundary k)) (by
      intro k l f
      apply Under.UnderMorphism.ext
      exact component_naturality f)

@[simp] theorem comparison_hom_right (k : SimplexCategory) :
    (comparison.hom.app k).right = singleCylinderToCE k := rfl

end

end DaggerModels.PartII.JTSingleCylinderCEIso
