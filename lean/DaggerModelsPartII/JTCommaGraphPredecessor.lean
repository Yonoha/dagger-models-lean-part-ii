import DaggerModelsPartII.JTInternalNecklaceGraphLift
import DaggerModelsPartII.JTGraphToPresentationArrow

/-!
# Every actual target-comma object receives a native graph presentation
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTCommaGraphPredecessor

open JTProjectiveOrderedFiberComparison OrderedNecklaceVertexPoints
open JTNecklaceEndpointCylinder

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev R (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}

private abbrev Pres := DecoratedCylinderNecklacePresentation.Presentation W x y
private abbrev labelCode (P : Pres (W := W) (x := x) (y := y)) :=
  OrderedLabelElements.necklace W (boundaryPoint W x y) P.base
private abbrev degree (P : Pres (W := W) (x := x) (y := y)) :=
  OrderedLabelElements.degree W (boundaryPoint W x y) P.base
private abbrev aug := NecklaceCylinderAugmentation.augmentation

variable (P : Pres (W := W) (x := x) (y := y))

private theorem augmentation_boundary :
    endpointInclusion P.fiber.left ≫
      (P.fiber.hom.right ≫ aug (labelCode P) (degree P)) = endpointInclusion (labelCode P) := by
  rw [← Category.assoc]
  have h : endpointInclusion P.fiber.left ≫ P.fiber.hom.right =
      (boundary (labelCode P)).app (degree P) := Under.w P.fiber.hom
  rw [h, NecklaceCylinderAugmentation.augmentation_boundary]

private theorem augmentation_endpoints :
    ((P.fiber.hom.right ≫ aug (labelCode P) (degree P)).app (op ⦋0⦌)
        P.fiber.left.first,
      (P.fiber.hom.right ≫ aug (labelCode P) (degree P)).app (op ⦋0⦌)
        P.fiber.left.last) = ((labelCode P).first, (labelCode P).last) := by
  have h := augmentation_boundary P
  dsimp only [endpointInclusion] at h
  rw [JTGeneralOrderedFiberWeak.orderedBoundary_natural] at h
  exact (JTEndpointObjects.boundaryHomEquiv _).symm.injective h

/-- The augmentation of an internal necklace preserves the two original
ordered endpoints and hence is an actual native code morphism. -/
def augmentationCode : P.fiber.left ⟶ labelCode P where
  map := P.fiber.hom.right ≫ aug (labelCode P) (degree P)
  first := congrArg Prod.fst (augmentation_endpoints P)
  last := congrArg Prod.snd (augmentation_endpoints P)

private def nativeInternal :=
  (BoundaryNecklaceComma.toNative
    ((DecoratedCylinderNecklacePresentation.underDiagram W x y).obj P.base)).obj P.fiber

/-- The native collapse and whole parameter of a graph lifting the
complete internal traversal of any actual decorated presentation. -/
theorem exists_graph_lift :
    ∃ (S : NecklaceCode) (c : S ⟶ P.fiber.left)
      (s : S.toSSet ⟶ GroupoidSimplex.parameter.obj (degree P)),
      lift (c ≫ augmentationCode P).map s ≫
        (cylinder (labelCode P)).app (degree P) = c.map ≫ P.fiber.hom.right := by
  obtain ⟨D⟩ := JTInternalNecklaceGraphLift.nonempty_lift (nativeInternal P)
  refine ⟨D.code, D.collapse, D.parameter, ?_⟩
  have h := D.comm
  change lift ((D.collapse.map ≫ P.fiber.hom.right) ≫ aug (labelCode P) (degree P))
      D.parameter ≫ (cylinder (labelCode P)).app (degree P) =
    D.collapse.map ≫ P.fiber.hom.right at h
  rw [Category.assoc] at h
  exact h

variable {Q : NecklacesOver (R W) (rawVertex W x) (rawVertex W y)}

/-- An arbitrary object of the actual target comma receives an arrow
from an actual graph presentation, over the same original target. -/
theorem exists_graph_predecessor
    (U : CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y) Q) :
    ∃ (S : NecklaceCode) (c : S ⟶ U.left.fiber.left)
      (s : S.toSSet ⟶ GroupoidSimplex.parameter.obj (degree U.left))
      (h : lift (c ≫ augmentationCode U.left).map s ≫
        (cylinder (labelCode U.left)).app (degree U.left) = c.map ≫ U.left.fiber.hom.right),
      Nonempty (JTGraphToPresentationArrow.graphToComma U S
        (c ≫ augmentationCode U.left) c s h ⟶ U) := by
  obtain ⟨S, c, s, h⟩ := exists_graph_lift U.left
  exact ⟨S, c, s, h, ⟨JTGraphToPresentationArrow.toComma Q U S
    (c ≫ augmentationCode U.left) c s h⟩⟩

end

end DaggerModels.PartII.JTCommaGraphPredecessor
