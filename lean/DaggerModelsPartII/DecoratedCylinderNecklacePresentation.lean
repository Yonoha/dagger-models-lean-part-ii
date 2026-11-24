import DaggerModelsPartII.BoundaryNecklaceComma
import DaggerModelsPartII.GrothendieckContractibleFibers
import DaggerModelsPartII.DecoratedNecklaceHomBar
import ActualNecklaceConeGadgetComparison
import NativeGroupoidCompletionNerveBaseCases

/-!
# The actual decorated cylinder necklace presentation

The base is the unchanged ordered-label Elements category. Each fiber is
the category of original native necklaces over its actual reduced cylinder.
The full descended-label cocone gives a strict functor to original necklaces
over the raw JT realization. No weakness of that target functor is asserted.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace
open DaggerOriginalProductGadget DaggerSSetGluing
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.DecoratedCylinderNecklacePresentation

open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open DecoratedNecklaceHomDiagram

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev R (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev v (W : Source) (x : (row W ⦋0⦌).obj (op ⦋0⦌)) :=
  JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x

variable (W : Source) (x y : (row W ⦋0⦌).obj (op ⦋0⦌))

/-- The SAME decorated cylinder, now retaining its fixed ordered boundary. -/
def underDiagram : Index W x y ⥤ Under JTXiEndpointCollapse.boundary :=
  OrderedLabelElements.projection W (boundaryPoint W x y) ⋙
    NecklaceCylinderJointDiagram.cylinderUnder

/-- The actual descended labels form a cocone UNDER the original boundary. -/
def underCocone : underDiagram W x y ⟶
    (Functor.const (Index W x y)).obj
      (JTConeMappingPresentation.targetUnder (R W) (v W x) (v W y)) where
  app i := Under.homMk
    (JTNecklaceEndpointCylinder.descend W x y
      (OrderedLabelElements.necklace W (boundaryPoint W x y) i)
      (OrderedLabelElements.degree W (boundaryPoint W x y) i)
      (OrderedLabelElements.label W (boundaryPoint W x y) i))
    (JTNecklaceEndpointCylinder.descend_boundary W x y
      (OrderedLabelElements.necklace W (boundaryPoint W x y) i)
      (OrderedLabelElements.degree W (boundaryPoint W x y) i)
      (OrderedLabelElements.label W (boundaryPoint W x y) i))
  naturality {i j} f := by
    apply Under.UnderMorphism.ext
    change (cylinderDiagram W x y).map f ≫
      (descendCocone W x y).ι.app j = (descendCocone W x y).ι.app i
    simpa only [Category.comp_id] using (descendCocone W x y).ι.naturality f

/-- The full parameter-aware category of actual original necklace presentations. -/
abbrev Presentation := BoundaryNecklaceComma.Presentation (underDiagram W x y)

/-- Forget the internal presentation, retaining the actual decorated index. -/
def projection : Presentation W x y ⥤ Index W x y :=
  Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram (underDiagram W x y))

/-- Postcompose each complete internal necklace by its actual descended label. -/
def toTarget : Presentation W x y ⥤ NecklacesOver (R W) (v W x) (v W y) :=
  BoundaryNecklaceComma.toTarget (underDiagram W x y) (underCocone W x y) ⋙
    BoundaryNecklaceComma.toNativeAt (R W) (v W x) (v W y)

/-- The target functor keeps the identical native necklace code. -/
theorem toTarget_obj_code (P : Presentation W x y) :
    ((toTarget W x y).obj P).code = P.fiber.left := rfl

/-- Its full original necklace map is the SAME map followed by actual descent. -/
theorem toTarget_obj_map (P : Presentation W x y) :
    ((toTarget W x y).obj P).map = P.fiber.hom.right ≫
      JTNecklaceEndpointCylinder.descend W x y
        (OrderedLabelElements.necklace W (boundaryPoint W x y) P.base)
        (OrderedLabelElements.degree W (boundaryPoint W x y) P.base)
        (OrderedLabelElements.label W (boundaryPoint W x y) P.base) := rfl

/-- Each original native presentation morphism is retained verbatim. -/
theorem toTarget_map_hom {P Q : Presentation W x y} (f : P ⟶ Q) :
    ((toTarget W x y).map f).hom = f.fiber.left := rfl

private theorem first_eq_cylinder (i : Index W x y) :
    BoundaryNecklaceComma.first ((underDiagram W x y).obj i) =
      NecklaceCylinderHomSpan.firstVertex
        (OrderedLabelElements.necklace W (boundaryPoint W x y) i)
        (OrderedLabelElements.degree W (boundaryPoint W x y) i) := by
  rw [BoundaryNecklaceComma.first_eq]
  rfl

private theorem last_eq_cylinder (i : Index W x y) :
    BoundaryNecklaceComma.last ((underDiagram W x y).obj i) =
      NecklaceCylinderHomSpan.lastVertex
        (OrderedLabelElements.necklace W (boundaryPoint W x y) i)
        (OrderedLabelElements.degree W (boundaryPoint W x y) i) := by
  rw [BoundaryNecklaceComma.last_eq]
  rfl

/-- Each actual cylinder's original endpoint Hom is weakly contractible. -/
private theorem cylinderHom_point_GW_at (T : NecklaceCode) (k : SimplexCategory) :
    GW (pointMap (NecklaceCylinderHomSpan.cylinderHom T k)) := by
  have hl : WeakEquivalence (NecklaceCylinderHomSpan.leftMap T k) :=
    NecklaceCylinderHomSpan.leftMap_weak T k
  have hs : WeakEquivalence (pointMap (NecklaceCylinderHomSpan.necklaceHom T)) :=
    (weakEquivalence_iff_GW _).mpr (DecoratedNecklaceHomBar.necklaceHom_point_GW T)
  have he : NecklaceCylinderHomSpan.leftMap T k ≫
      pointMap (NecklaceCylinderHomSpan.necklaceHom T) =
        pointMap (NecklaceCylinderHomSpan.cylinderHom T k) := pointIsTerminal.hom_ext _ _
  apply (weakEquivalence_iff_GW _).mp
  rw [← he]
  infer_instance

/-- The actual decorated cylinder Hom weight is weakly contractible, at each full label. -/
theorem cylinderHom_point_GW (i : Index W x y) :
    GW (pointMap ((cylinderHomDiagram W x y).obj i)) := by
  change GW (pointMap (NecklaceCylinderHomSpan.cylinderHom
    (OrderedLabelElements.necklace W (boundaryPoint W x y) i)
    (OrderedLabelElements.degree W (boundaryPoint W x y) i)))
  exact cylinderHom_point_GW_at
    (OrderedLabelElements.necklace W (boundaryPoint W x y) i)
    (OrderedLabelElements.degree W (boundaryPoint W x y) i)

/-- P2 transports that contraction to every SAME fiber necklace-index nerve. -/
theorem fiber_point_GW (i : Index W x y) :
    GW (pointMap (nerve ((BoundaryNecklaceComma.fiberDiagram
      (underDiagram W x y)).obj i))) := by
  let U := (underDiagram W x y).obj i
  let T := OrderedLabelElements.necklace W (boundaryPoint W x y) i
  let k := OrderedLabelElements.degree W (boundaryPoint W x y) i
  have hn : GW (pointMap
      (nerve (NecklacesOver U.right (BoundaryNecklaceComma.first U)
        (BoundaryNecklaceComma.last U)))) := by
    rw [first_eq_cylinder W x y i, last_eq_cylinder W x y i]
    exact DaggerActualNecklaceConeGadgetComparison.necklace_point_GW_of_original_hom
      ((JTNecklaceEndpointCylinder.value T).obj k)
      (NecklaceCylinderHomSpan.firstVertex T k)
      (NecklaceCylinderHomSpan.lastVertex T k)
      (cylinderHom_point_GW_at T k)
  have he : WeakEquivalence
      (nerveMap (BoundaryNecklaceComma.equivalence U).functor) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence _
  have hp : WeakEquivalence (pointMap
      (nerve (NecklacesOver U.right (BoundaryNecklaceComma.first U)
        (BoundaryNecklaceComma.last U)))) := (weakEquivalence_iff_GW _).mpr hn
  have hpoint : nerveMap (BoundaryNecklaceComma.equivalence U).functor ≫
      pointMap (nerve (NecklacesOver U.right (BoundaryNecklaceComma.first U)
        (BoundaryNecklaceComma.last U))) =
        pointMap (nerve (CostructuredArrow BoundaryNecklaceComma.necklaceUnder U)) :=
    pointIsTerminal.hom_ext _ _
  apply (weakEquivalence_iff_GW _).mp
  change WeakEquivalence (pointMap (nerve (CostructuredArrow
    BoundaryNecklaceComma.necklaceUnder U)))
  rw [← hpoint]
  infer_instance

/-- The original unlocalized Grothendieck projection is Kan weak. -/
theorem projection_weak : WeakEquivalence (nerveMap (projection W x y)) :=
  GrothendieckContractibleFibers.projection_weak
    (BoundaryNecklaceComma.fiberDiagram (underDiagram W x y))
    (fiber_point_GW W x y)

end

end DaggerModels.PartII.DecoratedCylinderNecklacePresentation
