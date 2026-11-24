import DaggerModelsPartII.JTCommaGraphPredecessor

/-!
# Transporting a native graph lift along an original presentation arrow
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphLiftTransport

open JTProjectiveOrderedFiberComparison OrderedNecklaceVertexPoints
open JTNecklaceEndpointCylinder
open JTCommaGraphPredecessor (augmentationCode)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev J := GroupoidSimplex.parameter

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}

abbrev Pres := DecoratedCylinderNecklacePresentation.Presentation W x y
abbrev Index := DecoratedNecklaceHomDiagram.Index W x y
abbrev projection := OrderedLabelElements.projection W (boundaryPoint W x y)
abbrev code (P : Pres (W := W) (x := x) (y := y)) :=
  OrderedLabelElements.necklace W (boundaryPoint W x y) P.base
abbrev degree (P : Pres (W := W) (x := x) (y := y)) :=
  OrderedLabelElements.degree W (boundaryPoint W x y) P.base

/-- A graph lift with the entire equation in the original cylinder. -/
@[ext]
structure GraphLift (P : Pres (W := W) (x := x) (y := y)) (S : NecklaceCode) where
  collapse : S ⟶ P.fiber.left
  parameter : S.toSSet ⟶ J.obj (degree P)
  comm : lift (collapse ≫ augmentationCode P).map parameter ≫ (cylinder (code P)).app (degree P) =
    collapse.map ≫ P.fiber.hom.right

variable {P P' P'' : Pres (W := W) (x := x) (y := y)}
variable {S : NecklaceCode}

abbrev nativeOperator (a : P ⟶ P') : code P ⟶ code P' :=
  ((projection (W := W) (x := x) (y := y)).map a.base).1

abbrev degreeOperator (a : P ⟶ P') : degree P ⟶ degree P' :=
  ((projection (W := W) (x := x) (y := y)).map a.base).2

/-- An original presentation arrow respects the whole cylinder traversal. -/
theorem traversal_natural (a : P ⟶ P') :
    a.fiber.left.map ≫ P'.fiber.hom.right =
      P.fiber.hom.right ≫
        (nativeMap (nativeOperator a) (degree P) ≫ (value (code P')).map (degreeOperator a)) := by
  exact congrArg (fun h ↦ h.right) (CostructuredArrow.w a.fiber)

/-- The induced map between the original static necklaces is a native operator. -/
theorem augmentationCode_natural (a : P ⟶ P') :
    a.fiber.left ≫ augmentationCode P' = augmentationCode P ≫ nativeOperator a := by
  apply NecklaceCode.Hom.ext
  change a.fiber.left.map ≫ (P'.fiber.hom.right ≫
      NecklaceCylinderAugmentation.augmentation (code P') (degree P')) =
    (P.fiber.hom.right ≫ NecklaceCylinderAugmentation.augmentation (code P) (degree P)) ≫
      (nativeOperator a).map
  rw [← Category.assoc, traversal_natural a, Category.assoc,
    Category.assoc (nativeMap (nativeOperator a) (degree P)),
    NecklaceCylinderAugmentation.augmentation_parameter_natural,
    NecklaceCylinderAugmentation.augmentation_native_natural, Category.assoc]

private theorem lift_cylinder_joint (a : P ⟶ P') (f : S.toSSet ⟶ (code P).toSSet)
    (s : S.toSSet ⟶ J.obj (degree P)) :
    (lift f s ≫ (cylinder (code P)).app (degree P)) ≫
      (nativeMap (nativeOperator a) (degree P) ≫ (value (code P')).map (degreeOperator a)) =
    lift (f ≫ (nativeOperator a).map) (s ≫ J.map (degreeOperator a)) ≫
      (cylinder (code P')).app (degree P') := by
  simp only [Category.assoc]
  rw [← Category.assoc ((cylinder (code P)).app (degree P)),
    nativeMap_cylinder, Category.assoc, ← (cylinder (code P')).naturality (degreeOperator a)]
  simp only [← Category.assoc]
  congr 1

/-- Transport a specified graph lift along an arbitrary original arrow, keeping the code. -/
def GraphLift.transport (D : GraphLift P S) (a : P ⟶ P') : GraphLift P' S where
  collapse := D.collapse ≫ a.fiber.left
  parameter := D.parameter ≫ J.map (degreeOperator a)
  comm := by
    have h : (D.collapse ≫ a.fiber.left) ≫ augmentationCode P' =
        (D.collapse ≫ augmentationCode P) ≫ nativeOperator a := by
      rw [Category.assoc, augmentationCode_natural a, Category.assoc]
    rw [h]
    change lift ((D.collapse ≫ augmentationCode P).map ≫ (nativeOperator a).map)
      (D.parameter ≫ J.map (degreeOperator a)) ≫ (cylinder (code P')).app (degree P') =
      (D.collapse.map ≫ a.fiber.left.map) ≫ P'.fiber.hom.right
    rw [← lift_cylinder_joint, D.comm, Category.assoc, Category.assoc, traversal_natural a]

/-- The resulting horizontal code is the composite of the original native operators. -/
theorem GraphLift.horizontal_transport (D : GraphLift P S) (a : P ⟶ P') :
    (D.transport a).collapse ≫ augmentationCode P' =
      (D.collapse ≫ augmentationCode P) ≫ nativeOperator a := by
  change (D.collapse ≫ a.fiber.left) ≫ augmentationCode P' = _
  rw [Category.assoc, augmentationCode_natural a, Category.assoc]

private abbrev internalCode := BoundaryNecklaceComma.sourceCode
  (DecoratedCylinderNecklacePresentation.underDiagram W x y)
private abbrev parameterObject := DecoratedCylinderNecklacePresentation.projection W x y ⋙
  projection (W := W) (x := x) (y := y) ⋙ CategoryTheory.Prod.snd NecklaceCode SimplexCategory ⋙ J

/-- Identity transport preserves both original components. -/
theorem GraphLift.transport_id (D : GraphLift P S) : D.transport (𝟙 P) = D := by
  apply GraphLift.ext
  · change D.collapse ≫ internalCode.map (𝟙 P) = D.collapse
    rw [CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  · change D.parameter ≫ parameterObject.map (𝟙 P) = D.parameter
    rw [CategoryTheory.Functor.map_id]
    exact Category.comp_id _

/-- Transport along composable original arrows is strict on the graph data. -/
theorem GraphLift.transport_comp (D : GraphLift P S) (a : P ⟶ P') (b : P' ⟶ P'') :
    (D.transport a).transport b = D.transport (a ≫ b) := by
  apply GraphLift.ext
  · change (D.collapse ≫ internalCode.map a) ≫ internalCode.map b =
      D.collapse ≫ internalCode.map (a ≫ b)
    rw [Functor.map_comp, Category.assoc]
  · change (D.parameter ≫ parameterObject.map a) ≫ parameterObject.map b =
      D.parameter ≫ parameterObject.map (a ≫ b)
    rw [Functor.map_comp, Category.assoc]

end

end DaggerModels.PartII.JTGraphLiftTransport
