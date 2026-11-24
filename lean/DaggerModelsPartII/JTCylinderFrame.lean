import DaggerModelsPartII.ReducedCylinderColimits

/-!
# The standard-simplex reduced cylinder with its original ordered boundary

This is the literal reduced cylinder evaluated on the standard simplex,
as an under-boundary cosimplicial diagram. Its augmentation forgets the
standard-simplex factor and retains both original pushout legs.
-/

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory Simplicial

namespace DaggerModels.PartII.JTCylinderFrame

open JTXiEndpointCollapse

noncomputable section

/-- The literal ordered boundary inclusion into the ordinary interval. -/
def j : JTXiEndpointCollapse.boundary ⟶ interval := (SSet.boundary 1).ι

instance : Mono j := by
  dsimp only [j]
  infer_instance

/-- The actual reduced cylinder on each standard simplex, under the same boundary. -/
def under : SimplexCategory ⥤ Under JTXiEndpointCollapse.boundary :=
  SSet.stdSimplex.{0} ⋙ ReducedCylinder.functor j

/-- The underlying actual reduced-cylinder cosimplicial simplicial set. -/
def value : SimplexCategory ⥤ SSet.{0} :=
  SSet.stdSimplex.{0} ⋙ ReducedCylinder.value j

/-- The ordered boundary of the actual standard-simplex reduced cylinder. -/
def boundary : (Functor.const SimplexCategory).obj JTXiEndpointCollapse.boundary ⟶
    value :=
  Functor.whiskerLeft SSet.stdSimplex.{0} (ReducedCylinder.boundary j)

/-- The underlying interval-cylinder leg at the specified parameter. -/
def cylinder (k : SimplexCategory) : interval ⊗ SSet.stdSimplex.obj k ⟶ value.obj k :=
  (ReducedCylinder.cylinder j).app (SSet.stdSimplex.obj k)

@[simp] theorem under_obj_hom (k : SimplexCategory) :
    (under.obj k).hom = boundary.app k := rfl

@[simp] theorem under_map_right {k l : SimplexCategory} (f : k ⟶ l) :
    (under.map f).right = value.map f := rfl

/-- The same literal under-boundary diagram expressed by its structure transformation. -/
theorem under_eq_lift : under = Under.lift value boundary := rfl

private theorem projection_compatibility :
    ReducedCylinder.tensorInclusion j ≫ ReducedCylinder.tensorProjection interval =
      ReducedCylinder.tensorProjection JTXiEndpointCollapse.boundary ≫
        (Functor.const SSet.{0}).map j := by
  apply NatTrans.ext
  funext K
  change (j ⊗ₘ 𝟙 K) ≫ CartesianMonoidalCategory.fst interval K =
    CartesianMonoidalCategory.fst JTXiEndpointCollapse.boundary K ≫ j
  exact CartesianMonoidalCategory.tensorHom_fst j (𝟙 K)

private def augmentationAll : ReducedCylinder.value j ⟶
    (Functor.const SSet.{0}).obj interval :=
  pushout.desc (ReducedCylinder.tensorProjection interval)
    ((Functor.const SSet.{0}).map j) projection_compatibility

/-- The actual natural augmentation forgets only the standard-simplex factor. -/
def augmentation : value ⟶ (Functor.const SimplexCategory).obj interval :=
  Functor.whiskerLeft SSet.stdSimplex.{0} augmentationAll

/-- On the uncollapsed cylinder, augmentation is the literal first projection. -/
theorem cylinder_augmentation (k : SimplexCategory) :
    cylinder k ≫ augmentation.app k =
      CartesianMonoidalCategory.fst interval (SSet.stdSimplex.obj k) := by
  exact NatTrans.congr_app
    (pushout.inl_desc (ReducedCylinder.tensorProjection interval)
      ((Functor.const SSet.{0}).map j) projection_compatibility)
    (SSet.stdSimplex.obj k)

/-- On the ordered boundary, augmentation is the original inclusion. -/
theorem boundary_augmentation (k : SimplexCategory) :
    boundary.app k ≫ augmentation.app k = j := by
  exact NatTrans.congr_app
    (pushout.inr_desc (ReducedCylinder.tensorProjection interval)
      ((Functor.const SSet.{0}).map j) projection_compatibility)
    (SSet.stdSimplex.obj k)

/-- The literal two-legged reduced-cylinder universal property, in every degree. -/
theorem isPushout (k : SimplexCategory) :
    IsPushout ((ReducedCylinder.tensorInclusion j).app (SSet.stdSimplex.obj k))
      ((ReducedCylinder.tensorProjection JTXiEndpointCollapse.boundary).app
        (SSet.stdSimplex.obj k)) (cylinder k) (boundary.app k) :=
  ReducedCylinder.value_isPushout j

end

end DaggerModels.PartII.JTCylinderFrame
