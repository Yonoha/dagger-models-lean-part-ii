import DaggerModelsPartII.JTInterpolatedReducedCylinder
import DaggerModelsPartII.JTParametrizedTargetLiftTransport

/-! An arbitrary groupoid time map acts on the actual endpoint-collapsed cylinder. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open DaggerModels DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTInterpolatedCylinderParameterTime

open JTNecklaceEndpointCylinder (under value cylinder boundary isPushout)
open JTInterpolatedReducedCylinder (cylinderMap cylinderMap_cylinder cylinderMap_boundary)
open NecklaceCylinderAugmentation (augmentation augmentation_cylinder augmentation_boundary)

noncomputable section

private abbrev J := GroupoidSimplex.parameter

variable (T : NecklaceCode) {m n k : SimplexCategory} (r : J.obj m ⟶ J.obj n)

/-- The time map keeps both original endpoints and the whole native necklace. -/
def changeTime : (under T).obj m ⟶ (under T).obj n :=
  Under.homMk (cylinderMap T (snd T.toSSet (J.obj m) ≫ r)) (cylinderMap_boundary T _)

theorem changeTime_cylinder :
    (cylinder T).app m ≫ (changeTime T r).right = (T.toSSet ◁ r) ≫ (cylinder T).app n := by
  change (cylinder T).app m ≫ cylinderMap T (snd T.toSSet (J.obj m) ≫ r) = _
  rw [cylinderMap_cylinder]
  congr 1

theorem changeTime_boundary :
    (boundary T).app m ≫ (changeTime T r).right = (boundary T).app n :=
  cylinderMap_boundary T _

/-- Changing time and then evaluating a graph uses the actual pullback graph. -/
theorem changeTime_cylinderMap (p : T.toSSet ⊗ J.obj n ⟶ J.obj k) :
    (changeTime T r).right ≫ cylinderMap T p = cylinderMap T ((T.toSSet ◁ r) ≫ p) := by
  apply (isPushout T m).hom_ext
  · rw [← Category.assoc, changeTime_cylinder, Category.assoc, cylinderMap_cylinder,
      cylinderMap_cylinder, ← Category.assoc]
    congr 1
  · rw [← Category.assoc, changeTime_boundary, cylinderMap_boundary, cylinderMap_boundary]

/-- The full projection to the original native necklace is unchanged. -/
theorem changeTime_augmentation :
    (changeTime T r).right ≫ augmentation T n = augmentation T m := by
  apply (isPushout T m).hom_ext
  · rw [← Category.assoc, changeTime_cylinder, Category.assoc, augmentation_cylinder,
      augmentation_cylinder, whiskerLeft_fst]
  · rw [← Category.assoc, changeTime_boundary, augmentation_boundary, augmentation_boundary]

/-- The original simplex time operator is recovered on the actual cylinder. -/
theorem changeTime_of_simplex (j : m ⟶ n) : changeTime T (J.map j) = (under T).map j := by
  apply Under.UnderMorphism.ext
  apply (isPushout T m).hom_ext
  · rw [changeTime_cylinder]
    exact (cylinder T).naturality j
  · rw [changeTime_boundary]
    exact (Category.id_comp _).symm.trans ((boundary T).naturality j)

end

end DaggerModels.PartII.JTInterpolatedCylinderParameterTime
