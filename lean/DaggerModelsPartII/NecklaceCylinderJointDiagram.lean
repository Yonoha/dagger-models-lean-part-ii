import DaggerModelsPartII.NecklaceCylinderAugmentation
import Mathlib.CategoryTheory.Functor.Currying

/-!
# The actual necklace cylinder in both covariant operator directions

The two axes are the original native necklace maps and all simplex operators.
The boundary and augmentation are natural without choosing a parameter vertex.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.NecklaceCylinderJointDiagram

open JTNecklaceEndpointCylinder

noncomputable section

private abbrev NCode := NecklaceCode
private abbrev B := JTXiEndpointCollapse.boundary

/-- The original cylinder as a functor in both independent indices. -/
def curriedCylinder : NCode ⥤ SimplexCategory ⥤ SSet.{0} where
  obj := value
  map f :=
    { app := nativeMap f
      naturality := fun _ _ g ↦ nativeMap_parameter_natural f g }
  map_id T := by
    apply NatTrans.ext
    funext k
    exact nativeMap_id T k
  map_comp f g := by
    apply NatTrans.ext
    funext k
    exact nativeMap_comp f g k

/-- The actual covariant cylinder diagram on the product of both indices. -/
def cylinderDiagram : NCode × SimplexCategory ⥤ SSet.{0} :=
  Functor.uncurry.obj curriedCylinder

/-- The static necklace diagram, independent of the parameter degree. -/
def necklaceDiagram : NCode × SimplexCategory ⥤ SSet.{0} :=
  CategoryTheory.Prod.fst NCode SimplexCategory ⋙ NecklaceCode.simplicialFunctor

/-- Every joint cylinder map retains the same entire ordered boundary. -/
def cylinderBoundary :
    (Functor.const (NCode × SimplexCategory)).obj B ⟶ cylinderDiagram where
  app p := (boundary p.1).app p.2
  naturality {p q} f := by
    change 𝟙 B ≫ (boundary q.1).app q.2 =
      (boundary p.1).app p.2 ≫ (nativeMap f.1 p.2 ≫ (value q.1).map f.2)
    rw [Category.id_comp, ← Category.assoc, nativeMap_boundary]
    simpa only [Functor.const_obj_map, Category.id_comp] using
      (boundary q.1).naturality f.2

/-- The static diagram keeps the same two native endpoints. -/
def necklaceBoundary :
    (Functor.const (NCode × SimplexCategory)).obj B ⟶ necklaceDiagram where
  app p := endpointInclusion p.1
  naturality {_ _} f := by
    simpa only [Category.id_comp] using (endpointInclusion_natural f.1).symm

/-- The SAME original augmentation is natural for the full product category. -/
def augmentation : cylinderDiagram ⟶ necklaceDiagram where
  app p := NecklaceCylinderAugmentation.augmentation p.1 p.2
  naturality {p q} f := by
    change (nativeMap f.1 p.2 ≫ (value q.1).map f.2) ≫
        NecklaceCylinderAugmentation.augmentation q.1 q.2 =
      NecklaceCylinderAugmentation.augmentation p.1 p.2 ≫ f.1.map
    rw [Category.assoc, NecklaceCylinderAugmentation.augmentation_parameter_natural,
      NecklaceCylinderAugmentation.augmentation_native_natural]

/-- The augmentation preserves the boundary as a natural transformation. -/
theorem boundary_augmentation : cylinderBoundary ≫ augmentation = necklaceBoundary := by
  apply NatTrans.ext
  funext p
  exact NecklaceCylinderAugmentation.augmentation_boundary p.1 p.2

/-- The actual joint diagram under the fixed ordered boundary. -/
def cylinderUnder : NCode × SimplexCategory ⥤ Under B :=
  Under.lift cylinderDiagram cylinderBoundary

/-- The actual static necklace diagram under the same boundary. -/
def necklaceUnder : NCode × SimplexCategory ⥤ Under B :=
  Under.lift necklaceDiagram necklaceBoundary

end

end DaggerModels.PartII.NecklaceCylinderJointDiagram
