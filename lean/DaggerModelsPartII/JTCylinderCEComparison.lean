import DaggerModelsPartII.JTCylinderFrame
import DaggerModelsPartII.JTCEAugmentation
import DaggerModelsPartII.JTXiRelativeReedyFrame

/-!
# The standard-simplex cylinder maps to the actual CE cylinder

The ordinary simplex maps into its actual groupoid completion by the free
groupoid unit. The induced reduced-cylinder map preserves the literal
ordered boundary and the interval augmentation. No Joyal weakness of the
simplex-to-completion map is asserted.
-/

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory Simplicial DaggerModels

namespace DaggerModels.PartII.JTCylinderCEComparison

open JTXiEndpointCollapse GroupoidSimplex JTCylinderFrame

noncomputable section

/-- The identity ordered chain in the free groupoid on the ordered simplex,
viewed as a simplex of the actual completed parameter. -/
private def completionSimplex (k : SimplexCategory) :
    (parameter.obj k).obj (Opposite.op k) :=
  FreeGroupoid.of (Fin (k.len + 1))

/-- The literal free-groupoid unit on each standard simplex. -/
def simplexUnit : SSet.stdSimplex.{0} ⟶ parameter where
  app k := SSet.yonedaEquiv.symm (completionSimplex k)
  naturality k l f := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, SSet.stdSimplex.yonedaEquiv_map,
      SSet.yonedaEquiv_comp]
    change (SimplexCategory.toCat.map f).toFunctor ⋙
        FreeGroupoid.of (Fin (l.len + 1)) =
      FreeGroupoid.of (Fin (k.len + 1)) ⋙
        FreeGroupoid.map (SimplexCategory.toCat.map f).toFunctor
    exact congrArg Cat.Hom.toFunctor
      (Grpd.freeForgetAdjunction.unit.naturality (SimplexCategory.toCat.map f))

/-- The actual component is the Yoneda transpose of the original groupoid
completion unit, not an abstract map to an isomorphic parameter. -/
theorem simplexUnit_component (k : SimplexCategory) :
    simplexUnit.app k = SSet.yonedaEquiv.symm (completionSimplex k) := rfl

private def H : (SSet.{0} ⥤ SSet.{0}) ⥤ (SimplexCategory ⥤ SSet.{0}) :=
  (Functor.whiskeringLeft SimplexCategory SSet.{0} SSet.{0}).obj parameter

private local instance : PreservesColimitsOfSize.{0, 0} H := by
  dsimp [H]
  infer_instance

/-- Precomposition takes the variable-parameter reduced-cylinder pushout to
the actual functor-category pushout defining CE. -/
def parameterCEIso : parameter ⋙ ReducedCylinder.value JTCylinderFrame.j ≅ CE := by
  change H.obj (pushout (ReducedCylinder.tensorInclusion JTCylinderFrame.j)
      (ReducedCylinder.tensorProjection JTXiEndpointCollapse.boundary)) ≅
    pushout (H.map (ReducedCylinder.tensorInclusion JTCylinderFrame.j))
      (H.map (ReducedCylinder.tensorProjection JTXiEndpointCollapse.boundary))
  exact (PreservesPushout.iso H (ReducedCylinder.tensorInclusion JTCylinderFrame.j)
    (ReducedCylinder.tensorProjection JTXiEndpointCollapse.boundary)).symm

private theorem parameterCEIso_boundary :
    Functor.whiskerLeft parameter (ReducedCylinder.boundary JTCylinderFrame.j) ≫
      parameterCEIso.hom = CE_boundary := by
  change H.map (pushout.inr (ReducedCylinder.tensorInclusion JTCylinderFrame.j)
      (ReducedCylinder.tensorProjection JTXiEndpointCollapse.boundary)) ≫
        (PreservesPushout.iso H (ReducedCylinder.tensorInclusion JTCylinderFrame.j)
          (ReducedCylinder.tensorProjection JTXiEndpointCollapse.boundary)).inv =
    pushout.inr (H.map (ReducedCylinder.tensorInclusion JTCylinderFrame.j))
      (H.map (ReducedCylinder.tensorProjection JTXiEndpointCollapse.boundary))
  exact PreservesPushout.inr_iso_inv H
    (ReducedCylinder.tensorInclusion JTCylinderFrame.j)
    (ReducedCylinder.tensorProjection JTXiEndpointCollapse.boundary)

private theorem parameterCEIso_cylinder :
    Functor.whiskerLeft parameter (ReducedCylinder.cylinder JTCylinderFrame.j) ≫
      parameterCEIso.hom = CE_interval := by
  change H.map (pushout.inl (ReducedCylinder.tensorInclusion JTCylinderFrame.j)
      (ReducedCylinder.tensorProjection JTXiEndpointCollapse.boundary)) ≫
        (PreservesPushout.iso H (ReducedCylinder.tensorInclusion JTCylinderFrame.j)
          (ReducedCylinder.tensorProjection JTXiEndpointCollapse.boundary)).inv =
    pushout.inl (H.map (ReducedCylinder.tensorInclusion JTCylinderFrame.j))
      (H.map (ReducedCylinder.tensorProjection JTXiEndpointCollapse.boundary))
  exact PreservesPushout.inl_iso_inv H
    (ReducedCylinder.tensorInclusion JTCylinderFrame.j)
    (ReducedCylinder.tensorProjection JTXiEndpointCollapse.boundary)

/-- The map from the standard-simplex reduced cylinder to the original CE
pushout, natural in the ordinary simplex parameter. -/
def valueComparison : JTCylinderFrame.value ⟶ CE :=
  Functor.whiskerRight simplexUnit (ReducedCylinder.value JTCylinderFrame.j) ≫
    parameterCEIso.hom

/-- The ordered boundary remains literally the same map into CE. -/
theorem valueComparison_boundary :
    JTCylinderFrame.boundary ≫ valueComparison = CE_boundary := by
  apply NatTrans.ext
  funext k
  change (ReducedCylinder.boundary JTCylinderFrame.j).app
      (SSet.stdSimplex.obj k) ≫
      (ReducedCylinder.value JTCylinderFrame.j).map (simplexUnit.app k) ≫
      parameterCEIso.hom.app k = CE_boundary.app k
  rw [← Category.assoc,
    ← (ReducedCylinder.boundary JTCylinderFrame.j).naturality (simplexUnit.app k)]
  simpa only [Functor.const_obj_map, Category.id_comp] using
    (NatTrans.congr_app parameterCEIso_boundary k)

/-- The interval-cylinder leg uses the actual groupoid-completion unit. -/
theorem valueComparison_cylinder (k : SimplexCategory) :
    JTCylinderFrame.cylinder k ≫ valueComparison.app k =
      (𝟙 interval ⊗ₘ simplexUnit.app k) ≫ CE_interval.app k := by
  change (ReducedCylinder.cylinder JTCylinderFrame.j).app
      (SSet.stdSimplex.obj k) ≫
      (ReducedCylinder.value JTCylinderFrame.j).map (simplexUnit.app k) ≫
      parameterCEIso.hom.app k = _
  rw [← Category.assoc,
    ← (ReducedCylinder.cylinder JTCylinderFrame.j).naturality (simplexUnit.app k)]
  exact congrArg (fun f => (𝟙 interval ⊗ₘ simplexUnit.app k) ≫ f)
    (NatTrans.congr_app parameterCEIso_cylinder k)

/-- The comparison is an actual morphism under the original ordered
boundary, not just a map of the underlying simplicial sets. -/
def underComparison : JTCylinderFrame.under ⟶ Under.lift CE CE_boundary where
  app k := Under.homMk (valueComparison.app k)
    (NatTrans.congr_app valueComparison_boundary k)
  naturality k l f := by
    apply Under.UnderMorphism.ext
    exact valueComparison.naturality f

/-- The CE interval augmentation agrees with forgetting the standard-simplex
parameter on the literal reduced cylinder. -/
theorem valueComparison_augmentation :
    valueComparison ≫ JTCEAugmentation.CEAugmentation =
      JTCylinderFrame.augmentation := by
  apply NatTrans.ext
  funext k
  apply (JTCylinderFrame.isPushout k).hom_ext
  · change JTCylinderFrame.cylinder k ≫
        (valueComparison.app k ≫ JTCEAugmentation.CEAugmentation.app k) =
      JTCylinderFrame.cylinder k ≫ augmentation.app k
    rw [← Category.assoc, valueComparison_cylinder, Category.assoc,
      JTCEAugmentation.CEAugmentation_interval]
    calc
      _ = CartesianMonoidalCategory.fst interval (SSet.stdSimplex.obj k) := by
        simpa only [Category.comp_id] using
          (CartesianMonoidalCategory.tensorHom_fst
            (𝟙 interval) (simplexUnit.app k))
      _ = _ := (JTCylinderFrame.cylinder_augmentation k).symm
  · change JTCylinderFrame.boundary.app k ≫
        (valueComparison.app k ≫ JTCEAugmentation.CEAugmentation.app k) =
      JTCylinderFrame.boundary.app k ≫ augmentation.app k
    rw [← Category.assoc]
    have hb := NatTrans.congr_app valueComparison_boundary k
    change JTCylinderFrame.boundary.app k ≫ valueComparison.app k =
      CE_boundary.app k at hb
    rw [hb,
      JTCEAugmentation.CEAugmentation_boundary,
      JTCylinderFrame.boundary_augmentation]
    rfl

end

end DaggerModels.PartII.JTCylinderCEComparison
