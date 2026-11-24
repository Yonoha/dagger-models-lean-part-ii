import DaggerModelsPartII.JTGraphRefinementParameterArrow

/-!
# A graph arrow to an arbitrary decorated cylinder presentation

The native code map `f` is explicit: composing
with cylinder augmentation supplies an SSet map, but does not produce a native
necklace morphism in general.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTGraphToPresentationArrow

open JTProjectiveOrderedFiberComparison OrderedNecklaceLabelDiagram
open OrderedNecklaceVertexPoints JTRealizedLabelEndpoints
open JTGraphRefinement

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev J := GroupoidSimplex.parameter
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev R (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}

private abbrev code (P : DecoratedCylinderNecklacePresentation.Presentation W x y) :=
  OrderedLabelElements.necklace W (boundaryPoint W x y) P.base

private abbrev degree (P : DecoratedCylinderNecklacePresentation.Presentation W x y) :=
  OrderedLabelElements.degree W (boundaryPoint W x y) P.base

/-- Pull the actual ordered label of `P` back along the native map. -/
def pulledLabel (P : DecoratedCylinderNecklacePresentation.Presentation W x y)
    (S : NecklaceCode) (f : S ⟶ code P) :
    ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op S)).obj
      (op (degree P)) :=
  ((orderedNecklaceLabels W (boundaryPoint W x y)).map f.op).app
    (op (degree P)) (OrderedLabelElements.label W (boundaryPoint W x y) P.base)

/-- The whole-parameter graph presentation on the source necklace. -/
def graphPresentation (P : DecoratedCylinderNecklacePresentation.Presentation W x y)
    (S : NecklaceCode) (f : S ⟶ code P)
    (s : S.toSSet ⟶ J.obj (degree P)) :
    DecoratedCylinderNecklacePresentation.Presentation W x y :=
  presentation W x y S (degree P) (pulledLabel P S f) s

/-- The actual operator `(f, 𝟙 k)` in the category of ordered-label elements. -/
private def baseArrow (P : DecoratedCylinderNecklacePresentation.Presentation W x y)
    (S : NecklaceCode) (f : S ⟶ code P) :
    OrderedLabelElements.mk W (boundaryPoint W x y) S (degree P)
      (pulledLabel P S f) ⟶ P.base := by
  let L := orderedNecklaceLabels W (boundaryPoint W x y)
  let H := OrderedLabelElements.labelPresheaf W (boundaryPoint W x y)
  let g : (S, degree P) ⟶ (code P, degree P) := (f, 𝟙 (degree P))
  refine (CategoryOfElements.homMk P.base.unop
    (H.elementsMk (op (S, degree P)) (pulledLabel P S f)) g.op ?_).op
  change (L.obj (op S)).map (𝟙 (degree P)).op
    (((L.map f.op).app (op (degree P)))
      (OrderedLabelElements.label W (boundaryPoint W x y) P.base)) =
        pulledLabel P S f
  simp [pulledLabel, L]

private theorem graph_native (P : DecoratedCylinderNecklacePresentation.Presentation W x y)
    (S : NecklaceCode) (f : S ⟶ code P)
    (s : S.toSSet ⟶ J.obj (degree P)) :
    (CartesianMonoidalCategory.lift (𝟙 S.toSSet) s ≫
      (JTNecklaceEndpointCylinder.cylinder S).app (degree P)) ≫
        JTNecklaceEndpointCylinder.nativeMap f (degree P) =
      CartesianMonoidalCategory.lift f.map s ≫
        (JTNecklaceEndpointCylinder.cylinder (code P)).app (degree P) := by
  have hl : CartesianMonoidalCategory.lift (𝟙 S.toSSet) s ≫
      (f.map ⊗ₘ 𝟙 (J.obj (degree P))) =
        CartesianMonoidalCategory.lift f.map s := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, CartesianMonoidalCategory.tensorHom_fst,
        CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_fst_assoc,
        Category.id_comp]
    · simp only [Category.assoc, CartesianMonoidalCategory.tensorHom_snd,
        CartesianMonoidalCategory.lift_snd, Category.comp_id]
  rw [Category.assoc, JTNecklaceEndpointCylinder.nativeMap_cylinder,
    ← Category.assoc, hl]

/-- The fiber arrow uses the given native collapse, with the whole product
equality as its compatibility witness. -/
private def fiberArrow (P : DecoratedCylinderNecklacePresentation.Presentation W x y)
    (S : NecklaceCode) (f : S ⟶ code P)
    (c : S ⟶ P.fiber.left)
    (s : S.toSSet ⟶ J.obj (degree P))
    (h : CartesianMonoidalCategory.lift f.map s ≫
        (JTNecklaceEndpointCylinder.cylinder (code P)).app (degree P) =
      c.map ≫ P.fiber.hom.right) :
    ((BoundaryNecklaceComma.fiberDiagram
      (DecoratedCylinderNecklacePresentation.underDiagram W x y)).map
      (baseArrow P S f)).toFunctor.obj (graphPresentation P S f s).fiber ⟶
        P.fiber := by
  refine CostructuredArrow.homMk c ?_
  apply Under.UnderMorphism.ext
  change c.map ≫ P.fiber.hom.right =
    (CartesianMonoidalCategory.lift (𝟙 S.toSSet) s ≫
      (JTNecklaceEndpointCylinder.cylinder S).app (degree P)) ≫
        (JTNecklaceEndpointCylinder.nativeMap f (degree P) ≫
        (JTNecklaceEndpointCylinder.value (code P)).map (𝟙 (degree P)))
  rw [(JTNecklaceEndpointCylinder.value (code P)).map_id, Category.comp_id]
  exact h.symm.trans (graph_native P S f s).symm

/-- A genuine Grothendieck arrow from the graph on `S` to arbitrary `P`. -/
def toPresentation (P : DecoratedCylinderNecklacePresentation.Presentation W x y)
    (S : NecklaceCode) (f : S ⟶ code P)
    (c : S ⟶ P.fiber.left)
    (s : S.toSSet ⟶ J.obj (degree P))
    (h : CartesianMonoidalCategory.lift f.map s ≫
        (JTNecklaceEndpointCylinder.cylinder (code P)).app (degree P) =
      c.map ≫ P.fiber.hom.right) :
    graphPresentation P S f s ⟶ P where
  base := baseArrow P S f
  fiber := fiberArrow P S f c s h

/-- Postcompose the actual presentation arrow with an arbitrary target-comma
object over the original raw necklace target. -/
def graphToComma {Q : NecklacesOver (R W) (rawVertex W x) (rawVertex W y)}
    (U : CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y) Q)
    (S : NecklaceCode) (f : S ⟶ code U.left)
    (c : S ⟶ U.left.fiber.left)
    (s : S.toSSet ⟶ J.obj (degree U.left))
    (h : CartesianMonoidalCategory.lift f.map s ≫
        (JTNecklaceEndpointCylinder.cylinder (code U.left)).app (degree U.left) =
      c.map ≫ U.left.fiber.hom.right) :
    CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y) Q :=
  CostructuredArrow.mk (Y := graphPresentation U.left S f s)
    ((DecoratedCylinderNecklacePresentation.toTarget W x y).map
      (toPresentation U.left S f c s h) ≫ U.hom)

/-- The graph-to-comma object genuinely maps to the original target-comma object. -/
def toComma (Q : NecklacesOver (R W) (rawVertex W x) (rawVertex W y))
    (U : CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y) Q)
    (S : NecklaceCode) (f : S ⟶ code U.left)
    (c : S ⟶ U.left.fiber.left)
    (s : S.toSSet ⟶ J.obj (degree U.left))
    (h : CartesianMonoidalCategory.lift f.map s ≫
        (JTNecklaceEndpointCylinder.cylinder (code U.left)).app (degree U.left) =
      c.map ≫ U.left.fiber.hom.right) :
    graphToComma U S f c s h ⟶ U := by
  refine CostructuredArrow.homMk (toPresentation U.left S f c s h) ?_
  rfl

end

end DaggerModels.PartII.JTGraphToPresentationArrow
