import DaggerModelsPartII.JTGraphRefinement

/-!
# Increasing the parameter degree of a strict graph refinement

This construction retains the original native necklace code, its collapse to `Q`,
and the complete graph map.  It uses the actual arrow in the decorated
category of ordered labels and a fiber arrow over the identity native code.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTGraphRefinementParameterArrow

open DaggerModels.PartII
open JTGraphRefinement
open JTProjectiveOrderedFiberComparison OrderedNecklaceLabelDiagram
open OrderedNecklaceVertexPoints JTRealizedLabelEndpoints

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev R (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (R W) (rawVertex W x) (rawVertex W y)}

private theorem traversal_parameter (T : NecklaceCode) {k l : SimplexCategory}
    (j : k ⟶ l) (s : T.toSSet ⟶ J.obj k) :
    (CartesianMonoidalCategory.lift (𝟙 T.toSSet) s ≫
      (JTNecklaceEndpointCylinder.cylinder T).app k) ≫
        (JTNecklaceEndpointCylinder.value T).map j =
      CartesianMonoidalCategory.lift (𝟙 T.toSSet) (s ≫ J.map j) ≫
        (JTNecklaceEndpointCylinder.cylinder T).app l := by
  rw [Category.assoc, ← (JTNecklaceEndpointCylinder.cylinder T).naturality j,
    ← Category.assoc]
  congr 1
private theorem graph_parameter (D : Refinement W x y Q)
    {l : SimplexCategory} (j : D.degree ⟶ l)
    (u : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op D.code)).obj (op l))
    (hu : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op D.code)).map
      j.op u = D.label) :
    realizeGraph W l (D.parameter ≫ J.map j) (orderedLabel W x y D.code l u) =
      realizeGraph W D.degree D.parameter
        (orderedLabel W x y D.code D.degree D.label) := by
  let oldTraversal := CartesianMonoidalCategory.lift
    (𝟙 D.code.toSSet) D.parameter ≫
      (JTNecklaceEndpointCylinder.cylinder D.code).app D.degree
  let newTraversal := CartesianMonoidalCategory.lift
    (𝟙 D.code.toSSet) (D.parameter ≫ J.map j) ≫
      (JTNecklaceEndpointCylinder.cylinder D.code).app l
  have hnew : newTraversal ≫ JTNecklaceEndpointCylinder.descend W x y D.code l u =
      realizeGraph W l (D.parameter ≫ J.map j)
        (orderedLabel W x y D.code l u) := by
    change ((DecoratedCylinderNecklacePresentation.toTarget W x y).obj
      (presentation W x y D.code l u (D.parameter ≫ J.map j))).map = _
    exact presentation_target_map W x y D.code l u (D.parameter ≫ J.map j)
  have hold : oldTraversal ≫
      JTNecklaceEndpointCylinder.descend W x y D.code D.degree D.label =
      realizeGraph W D.degree D.parameter
        (orderedLabel W x y D.code D.degree D.label) := by
    change ((DecoratedCylinderNecklacePresentation.toTarget W x y).obj
      (presentation W x y D.code D.degree D.label D.parameter)).map = _
    exact presentation_target_map W x y D.code D.degree D.label D.parameter
  calc
    _ = newTraversal ≫ JTNecklaceEndpointCylinder.descend W x y D.code l u :=
      hnew.symm
    _ = oldTraversal ≫
          ((JTNecklaceEndpointCylinder.value D.code).map j ≫
            JTNecklaceEndpointCylinder.descend W x y D.code l u) := by
      simpa only [oldTraversal, newTraversal, Category.assoc] using
        congrArg (fun f ↦ f ≫ JTNecklaceEndpointCylinder.descend W x y D.code l u)
          (traversal_parameter D.code j D.parameter).symm
    _ = oldTraversal ≫ JTNecklaceEndpointCylinder.descend W x y D.code
          D.degree (((orderedNecklaceLabels W (boundaryPoint W x y)).obj
            (op D.code)).map j.op u) := by
      rw [JTNecklaceEndpointCylinder.descend_parameter_natural]
    _ = oldTraversal ≫ JTNecklaceEndpointCylinder.descend W x y D.code
          D.degree D.label := by rw [hu]
    _ = _ := hold

/-- Increase the parameter degree while keeping the native code and target
collapse literally unchanged. -/
def extendDegree (D : Refinement W x y Q) {l : SimplexCategory}
    (j : D.degree ⟶ l)
    (u : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op D.code)).obj (op l))
    (hu : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op D.code)).map
      j.op u = D.label) : Refinement W x y Q where
  code := D.code
  degree := l
  label := u
  parameter := D.parameter ≫ J.map j
  collapse := D.collapse
  comm := (graph_parameter D j u hu).trans D.comm

/-- The actual arrow of ordered-label elements. Its two operators are the
identity of the original necklace and the given parameter operator. -/
private def baseArrow (D : Refinement W x y Q) {l : SimplexCategory}
    (j : D.degree ⟶ l)
    (u : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op D.code)).obj (op l))
    (hu : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op D.code)).map
      j.op u = D.label) :
    OrderedLabelElements.mk W (boundaryPoint W x y) D.code D.degree D.label ⟶
      OrderedLabelElements.mk W (boundaryPoint W x y) D.code l u := by
  let P := OrderedLabelElements.labelPresheaf W (boundaryPoint W x y)
  let g : (D.code, D.degree) ⟶ (D.code, l) := (𝟙 D.code, j)
  refine (CategoryOfElements.homMk
    (P.elementsMk (op (D.code, l)) u)
    (P.elementsMk (op (D.code, D.degree)) D.label)
    g.op ?_).op
  let L := orderedNecklaceLabels W (boundaryPoint W x y)
  change (L.obj (op D.code)).map j.op ((L.map (𝟙 (op D.code))).app (op l) u) = D.label
  rw [L.map_id]
  exact hu

/-- The fiber component transports the same internal code through the
parameter cylinder map. -/
private def fiberArrow (D : Refinement W x y Q) {l : SimplexCategory}
    (j : D.degree ⟶ l)
    (u : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op D.code)).obj (op l))
    (hu : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op D.code)).map
      j.op u = D.label) :
    ((BoundaryNecklaceComma.fiberDiagram
      (DecoratedCylinderNecklacePresentation.underDiagram W x y)).map
      (baseArrow D j u hu)).toFunctor.obj
      (presentation W x y D.code D.degree D.label D.parameter).fiber ⟶
    (presentation W x y D.code l u (D.parameter ≫ J.map j)).fiber := by
  refine CostructuredArrow.homMk (𝟙 D.code) ?_
  apply Under.UnderMorphism.ext
  change (𝟙 D.code.toSSet) ≫
      (CartesianMonoidalCategory.lift (𝟙 D.code.toSSet)
        (D.parameter ≫ J.map j) ≫
        (JTNecklaceEndpointCylinder.cylinder D.code).app l) =
    (CartesianMonoidalCategory.lift (𝟙 D.code.toSSet) D.parameter ≫
      (JTNecklaceEndpointCylinder.cylinder D.code).app D.degree) ≫
        (JTNecklaceEndpointCylinder.nativeMap (𝟙 D.code) D.degree ≫
          (JTNecklaceEndpointCylinder.value D.code).map j)
  rw [Category.id_comp, JTNecklaceEndpointCylinder.nativeMap_id,
    Category.id_comp]
  exact (traversal_parameter D.code j D.parameter).symm

/-- A genuine Grothendieck arrow over the decorated label operator. -/
private def presentationArrow (D : Refinement W x y Q) {l : SimplexCategory}
    (j : D.degree ⟶ l)
    (u : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op D.code)).obj (op l))
    (hu : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op D.code)).map
      j.op u = D.label) :
    presentation W x y D.code D.degree D.label D.parameter ⟶
      presentation W x y D.code l u (D.parameter ≫ J.map j) where
  base := baseArrow D j u hu
  fiber := fiberArrow D j u hu

/-- The actual comma morphism lies over the identity of the native source
code; the target `Q` and its collapse are unchanged. -/
def toCommaArrow (D : Refinement W x y Q) {l : SimplexCategory}
    (j : D.degree ⟶ l)
    (u : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op D.code)).obj (op l))
    (hu : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op D.code)).map
      j.op u = D.label) :
    D.toComma ⟶ (extendDegree D j u hu).toComma := by
  refine CostructuredArrow.homMk (presentationArrow D j u hu) ?_
  apply NecklacesOver.Hom.ext
  change ((DecoratedCylinderNecklacePresentation.toTarget W x y).map
    (presentationArrow D j u hu)).hom ≫ D.collapse = D.collapse
  rw [DecoratedCylinderNecklacePresentation.toTarget_map_hom]
  change (𝟙 D.code) ≫ D.collapse = D.collapse
  exact Category.id_comp _

end

end DaggerModels.PartII.JTGraphRefinementParameterArrow
