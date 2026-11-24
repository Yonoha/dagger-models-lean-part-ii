import DaggerModelsPartII.JTGraphRestrictionRaw

/-!
# Transporting original graph predecessors over a fixed raw target
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphTransportRaw

open JTProjectiveOrderedFiberComparison OrderedNecklaceVertexPoints OrderedNecklaceLabelDiagram
open JTGraphLiftTransport
open JTCommaGraphPredecessor (augmentationCode)
open JTGraphRestrictionRaw (predecessor)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {P P' : Pres (W := W) (x := x) (y := y)} {S : NecklaceCode}

private abbrev L := orderedNecklaceLabels W (boundaryPoint W x y)
variable (D : GraphLift P S)

private abbrev horizontal := D.collapse ≫ augmentationCode P

private abbrev label := JTGraphToPresentationArrow.pulledLabel P S (horizontal D)

/-- The graph as an object of the actual decorated presentation. -/
private abbrev presentation := JTGraphToPresentationArrow.graphPresentation P S (horizontal D) D.parameter

private theorem label_transport (a : P ⟶ P') :
    ((L (W := W) (x := x) (y := y)).obj (op S)).map (degreeOperator a).op
      (label (D.transport a)) = label D := by
  let b := boundaryPoint W x y
  let F := orderedNecklaceLabels W b
  let f := horizontal D
  let g := nativeOperator a
  let j := degreeOperator a
  let v := OrderedLabelElements.label W b P'.base
  have h := OrderedLabelElements.label_map W b a.base
  change (F.obj (op S)).map j.op ((F.map (horizontal (D.transport a)).op).app (op (degree P')) v) =
    (F.map f.op).app (op (degree P)) (OrderedLabelElements.label W b P.base)
  have hw := congrFun ((F.map f.op).naturality j.op) ((F.map g.op).app (op (degree P')) v)
  change (F.map f.op).app (op (degree P))
      ((F.obj (op (code P))).map j.op ((F.map g.op).app (op (degree P')) v)) =
    (F.obj (op S)).map j.op ((F.map f.op).app (op (degree P'))
      ((F.map g.op).app (op (degree P')) v)) at hw
  have hh : horizontal (D.transport a) = f ≫ g := D.horizontal_transport a
  rw [hh, op_comp, Functor.map_comp, NatTrans.comp_app]
  change (F.obj (op S)).map j.op ((F.map f.op).app (op (degree P'))
      ((F.map g.op).app (op (degree P')) v)) = _
  exact hw.symm.trans (congrArg (fun z ↦ (F.map f.op).app (op (degree P)) z) h)

/-- The arrow of actual graph presentations obtained by transport. -/
def transportArrow (a : P ⟶ P') : presentation D ⟶ presentation (D.transport a) :=
  JTGraphPresentationOperator.presentationArrow (𝟙 S) (degreeOperator a)
    (label D) (label (D.transport a)) D.parameter (D.transport a).parameter
    (by simpa only [op_id, CategoryTheory.Functor.map_id, NatTrans.id_app, types_id_apply] using label_transport D a)
    (by exact (Category.id_comp _).symm)

theorem transportArrow_base (a : P ⟶ P') :
    (projection (W := W) (x := x) (y := y)).map (transportArrow D a).base =
      (𝟙 S, degreeOperator a) := rfl

theorem transportArrow_code (a : P ⟶ P') : (transportArrow D a).fiber.left = 𝟙 S := rfl


variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}

private abbrev F (W : Source) (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) :=
  DecoratedCylinderNecklacePresentation.toTarget W x y

variable {U V : CostructuredArrow (F W x y) Q}

/-- Transport of a graph lift is an actual arrow over the fixed raw target. -/
def commaTransport (D : GraphLift U.left S) (a : U ⟶ V) :
    predecessor D ⟶ predecessor (D.transport a.left) := by
  refine CostructuredArrow.homMk (transportArrow D a.left) ?_
  apply NecklacesOver.Hom.ext
  change ((F W x y).map (transportArrow D a.left)).hom ≫
    ((D.transport a.left).collapse ≫ V.hom.hom) = D.collapse ≫ U.hom.hom
  rw [DecoratedCylinderNecklacePresentation.toTarget_map_hom, transportArrow_code]
  have hw := congrArg (fun f : (F W x y).obj U.left ⟶ Q ↦ f.hom) (CostructuredArrow.w a)
  change a.left.fiber.left ≫ V.hom.hom = U.hom.hom at hw
  change 𝟙 S ≫ ((D.collapse ≫ a.left.fiber.left) ≫ V.hom.hom) = _
  exact (Category.id_comp _).trans ((Category.assoc _ _ _).trans
    (congrArg (fun f ↦ D.collapse ≫ f) hw))

theorem commaTransport_code (D : GraphLift U.left S) (a : U ⟶ V) :
    (commaTransport D a).left.fiber.left = 𝟙 S := rfl

end

end DaggerModels.PartII.JTGraphTransportRaw
