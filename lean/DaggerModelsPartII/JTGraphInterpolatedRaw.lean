import DaggerModelsPartII.JTInterpolatedReducedCylinder
import DaggerModelsPartII.JTGraphParameterFiber
import DaggerModelsPartII.JTGraphFactoredPresentation

/-!
# Interpolated graph traversals retain the exact fixed native target
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphInterpolatedRaw

open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTGraphLiftTransport
open JTCommaGraphPredecessor (augmentationCode)
open JTGraphToPresentationArrow (pulledLabel)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphParameterInterpolation (interpolate)
open JTNecklaceEndpointCylinder
open JTInterpolatedReducedCylinder (cylinderMap cylinderMap_cylinder cylinderMap_boundary)
open NecklaceCylinderAugmentation (augmentation augmentation_cylinder augmentation_boundary)
open DecoratedCylinderNecklacePresentation (underDiagram underCocone)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev J := GroupoidSimplex.parameter
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

private theorem native_graph {X : SSet.{0}} {S T : NecklaceCode} (f : S ⟶ T)
    (k : SimplexCategory) (h : X ⟶ S.toSSet) (p : X ⟶ J.obj k) :
    (lift h p ≫ (cylinder S).app k) ≫ nativeMap f k =
      lift (h ≫ f.map) p ≫ (cylinder T).app k := by
  rw [Category.assoc, nativeMap_cylinder, ← Category.assoc]
  congr 1

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {S : NecklaceCode} {n : SimplexCategory}
variable (U : TargetComma Q) (c : S ⟶ U.left.fiber.left)

/-- The pullback of the original label to the fixed source code. -/
def index : DecoratedNecklaceHomDiagram.Index W x y :=
  OrderedLabelElements.mk W (boundaryPoint W x y) S (degree U.left)
    (pulledLabel U.left S (c ≫ augmentationCode U.left))

/-- A time-dependent parameter as a morphism under the ordered endpoints. -/
def toDecoratedBy (p : S.toSSet ⊗ J.obj n ⟶ J.obj (degree U.left)) :
    (under S).obj n ⟶ (underDiagram W x y).obj (index U c) :=
  Under.homMk (cylinderMap S p) (cylinderMap_boundary S p)

/-- Interpolate a prescribed family in the unchanged decorated cylinder. -/
def toDecorated (s : Fin (n.len + 1) → (S.toSSet ⟶ J.obj (degree U.left))) :
    (under S).obj n ⟶ (underDiagram W x y).obj (index U c) :=
  toDecoratedBy U c (interpolate s)

variable (p : S.toSSet ⊗ J.obj n ⟶ J.obj (degree U.left))

/-- The complete interpolated cylinder maps to the exact original traversal. -/
theorem whole_cylinder_by
    (hp : lift (fst S.toSSet (J.obj n) ≫ (c ≫ augmentationCode U.left).map) p ≫
      (cylinder (code U.left)).app (degree U.left) =
        fst S.toSSet (J.obj n) ≫ c.map ≫ U.left.fiber.hom.right) :
    (toDecoratedBy U c p).right ≫ nativeMap (c ≫ augmentationCode U.left) (degree U.left) =
      augmentation S n ≫ c.map ≫ U.left.fiber.hom.right := by
  let k := degree U.left
  let f := c ≫ augmentationCode U.left
  let u := c.map ≫ U.left.fiber.hom.right
  change cylinderMap S p ≫ nativeMap f k = augmentation S n ≫ u
  apply (isPushout S n).hom_ext
  · rw [← Category.assoc ((cylinder S).app n), cylinderMap_cylinder, native_graph,
      ← Category.assoc ((cylinder S).app n), augmentation_cylinder]
    exact hp
  · rw [← Category.assoc ((boundary S).app n), cylinderMap_boundary, nativeMap_boundary,
      ← Category.assoc ((boundary S).app n), augmentation_boundary]
    change (boundary (code U.left)).app k = endpointInclusion S ≫ c.map ≫ U.left.fiber.hom.right
    rw [← Category.assoc, endpointInclusion_natural]
    exact (Under.w U.left.fiber.hom).symm

/-- The exact native comparison to the original raw target is constant
in time on the whole interpolated cylinder. -/
theorem whole_raw_by
    (hp : lift (fst S.toSSet (J.obj n) ≫ (c ≫ augmentationCode U.left).map) p ≫
      (cylinder (code U.left)).app (degree U.left) =
        fst S.toSSet (J.obj n) ≫ c.map ≫ U.left.fiber.hom.right) :
    (toDecoratedBy U c p).right ≫ ((underCocone W x y).app (index U c)).right =
      augmentation S n ≫ (c ≫ U.hom.hom).map ≫ Q.map := by
  let d := ((underCocone W x y).app U.left.base).right
  have hlabel : nativeMap (c ≫ augmentationCode U.left) (degree U.left) ≫ d =
      ((underCocone W x y).app (index U c)).right :=
    descend_native_natural W x y (c ≫ augmentationCode U.left) (degree U.left)
      (OrderedLabelElements.label W (boundaryPoint W x y) U.left.base)
  have hu : U.hom.hom.map ≫ Q.map = U.left.fiber.hom.right ≫ d := U.hom.w
  calc
    _ = ((toDecoratedBy U c p).right ≫ nativeMap (c ≫ augmentationCode U.left)
          (degree U.left)) ≫ d := by rw [Category.assoc, hlabel]
    _ = (augmentation S n ≫ c.map ≫ U.left.fiber.hom.right) ≫ d :=
      congrArg (fun h ↦ h ≫ d) (whole_cylinder_by U c p hp)
    _ = augmentation S n ≫ c.map ≫ (U.left.fiber.hom.right ≫ d) := by
      simp only [Category.assoc]
    _ = augmentation S n ≫ (c ≫ U.hom.hom).map ≫ Q.map := by
      rw [← hu]
      change augmentation S n ≫ c.map ≫ U.hom.hom.map ≫ Q.map = _
      exact congrArg (fun h ↦ augmentation S n ≫ h) (Category.assoc _ _ _).symm

/-- The prescribed finite family realizes the same exact native comparison. -/
theorem whole_raw
    (s : Fin (n.len + 1) → (S.toSSet ⟶ J.obj (degree U.left)))
    (hs : ∀ i, lift (c ≫ augmentationCode U.left).map (s i) ≫
      (cylinder (code U.left)).app (degree U.left) = c.map ≫ U.left.fiber.hom.right) :
    (toDecorated U c s).right ≫ ((underCocone W x y).app (index U c)).right =
      augmentation S n ≫ (c ≫ U.hom.hom).map ≫ Q.map :=
  whole_raw_by U c (interpolate s)
    (JTGraphParameterFiber.interpolate_fiber (code U.left) (degree U.left) n
      (c ≫ augmentationCode U.left).map s (c.map ≫ U.left.fiber.hom.right) hs)

end

end DaggerModels.PartII.JTGraphInterpolatedRaw
