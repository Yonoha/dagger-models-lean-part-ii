import DaggerModelsPartII.JTGraphSpanFixedTargetData
import DaggerModelsPartII.JTGraphVariableComparisonConesOperators
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-! Evaluation of the original simplex spans with both native and coefficient transport. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphSpanLift

open JTGraphFactoredPresentation (TargetComma)
open JTProjectiveOrderedFiberComparison (row)
open JTGraphCylinderSimplexSpan (SpanIndex smaller degree index)
open JTGraphSpanFamily (tail head traversal)
open JTGraphCylinderSpanProjection (nativeCode)
open JTGraphSpanParameterMap (parameter)
open JTGraphVariableTimeIndex (toNative)
open JTGraphVariableTimeTransport (transport)
open JTGraphVariableTimeTraversal (labels)
open JTGraphVariableLabelTransport (labelTransport labelTransport_projection)
open JTParametrizedTargetFamilies (Family codes)
open JTGraphVariableTimeComparison (decoratedCollapse nativeCollapse)
open JTGraphVariableComparisonConesOperators (label_triangle)
open JTGraphLiftTransport (degreeOperator)
open OrderedNecklaceVertexPoints (boundaryPoint)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))

private abbrev C := TargetComma Q
private abbrev S := SpanIndex (C Q)
private abbrev L := DecoratedNecklaceHomDiagram.Index W x y
private abbrev proj := OrderedLabelElements.projection W (boundaryPoint W x y)
private abbrev originalLabel :=
  CostructuredArrow.proj (DecoratedCylinderNecklacePresentation.toTarget W x y) Q ⋙
    DecoratedCylinderNecklacePresentation.projection W x y
private abbrev jointIndex := index (C Q) (nativeCode Q)
private abbrev nativeIndex := (jointIndex Q) ⋙ CategoryTheory.Prod.fst _ _

/-- The actual smaller simplex supplies the time at each indexed span. -/
abbrev time := smaller (C Q) ⋙ degree (C Q)

private abbrev ops : S Q ⥤ NecklaceCode × SimplexCategory :=
  (nativeIndex Q).prod' (tail (C Q) ⋙ originalLabel Q ⋙ proj ⋙ CategoryTheory.Prod.snd _ _)

private instance : (proj (W := W) (x := x) (y := y)).Faithful := by
  change ((CategoryOfElements.π _).leftOp).Faithful
  infer_instance

private def labelObj (P : S Q) : L (W := W) (x := x) (y := y) :=
  JTGraphSpanFixedTargetData.labelAt (W := W) (x := x) (y := y) (Q := Q) P

set_option maxHeartbeats 650000 in
private def nativeOp {P P' : S Q} (f : P ⟶ P') :
    (toNative ((tail (C Q)).obj P')).obj
        ((transport ((tail (C Q)).map f)).obj (parameter (Q := Q) P)) ⟶
      (toNative ((tail (C Q)).obj P')).obj (parameter (Q := Q) P') :=
  Over.homMk ((head (C Q) ⋙ nativeCode Q).map f) (by
    change (nativeCode Q).map ((head (C Q)).map f) ≫
      (nativeCode Q).map ((traversal (C := C Q)).app P') =
      (nativeCode Q).map ((traversal (C := C Q)).app P) ≫
        (nativeCode Q).map ((tail (C Q)).map f)
    rw [← (nativeCode Q).map_comp, ← (nativeCode Q).map_comp]
    exact (nativeCode Q).congr_map ((traversal (C := C Q)).naturality f))

set_option maxHeartbeats 650000 in
private def labelMap {P P' : S Q} (f : P ⟶ P') : labelObj Q P ⟶ labelObj Q P' := by
  let U := (tail (C Q)).obj P
  let V := (tail (C Q)).obj P'
  let a : U ⟶ V := (tail (C Q)).map f
  let p : JTGraphVariableTimeIndex.Index U := parameter (Q := Q) P
  let p' : JTGraphVariableTimeIndex.Index V := parameter (Q := Q) P'
  change (labels U).obj p ⟶ (labels V).obj p'
  refine (labelTransport a).app p ≫ ?_
  exact (JTGraphNativeLabelDiagram.diagram V).map (nativeOp Q f)

private theorem labelMap_projection {P P' : S Q} (f : P ⟶ P') :
    proj.map (labelMap Q f) = (ops Q).map f := by
  let V := (tail (C Q)).obj P'
  let a := (tail (C Q)).map f
  let g := nativeOp Q f
  rw [labelMap]
  simp only [id_eq]
  rw [proj.map_comp, labelTransport_projection]
  have hb := JTGraphNativeLabelDiagram.diagram_map V g
  change proj.map ((JTGraphNativeLabelDiagram.diagram V).map g) = _ at hb
  rw [hb]
  change (𝟙 _ ≫ g.left, degreeOperator a.left ≫ 𝟙 _) = _
  rw [Category.id_comp, Category.comp_id]
  rfl

/-- The decoration of an original span preserves identity and composition. -/
def spanLabels : S Q ⥤ L (W := W) (x := x) (y := y) :=
  Functor.Faithful.div (ops Q) proj (labelObj Q) (fun _ ↦ rfl) (labelMap Q)
    (fun {_ _} {f} ↦ heq_of_eq (labelMap_projection Q f))

/-- The original decorated collapse is natural along all span operators. -/
def spanLabelCollapse : spanLabels Q ⟶ tail (C Q) ⋙ originalLabel Q where
  app P := (decoratedCollapse ((tail (C Q)).obj P)).app (parameter (Q := Q) P)
  naturality {P P'} f := by
    let U := (tail (C Q)).obj P
    let V := (tail (C Q)).obj P'
    let a : U ⟶ V := (tail (C Q)).map f
    let p : JTGraphVariableTimeIndex.Index U := parameter (Q := Q) P
    let p' : JTGraphVariableTimeIndex.Index V := parameter (Q := Q) P'
    let g := nativeOp Q f
    change ((labelTransport a).app p ≫
        (JTGraphNativeLabelDiagram.diagram V).map g) ≫
      (decoratedCollapse V).app p' =
        (decoratedCollapse U).app p ≫ a.left.base
    rw [Category.assoc]
    have hn := (JTGraphNativeLabelDiagram.toOriginal V).naturality g
    change (JTGraphNativeLabelDiagram.diagram V).map g ≫
        (decoratedCollapse V).app p' =
      (decoratedCollapse V).app ((transport a).obj p) ≫ 𝟙 _ at hn
    rw [hn, Category.comp_id]
    exact label_triangle a p

private theorem spanLabels_projection {P P' : S Q} (f : P ⟶ P') :
    proj.map ((spanLabels Q).map f) = (ops Q).map f := labelMap_projection Q f

private abbrev targetCollapse (U : C Q) := U.hom.hom

set_option maxHeartbeats 550000 in
private def collapse : codes (spanLabels Q) ⟶ (Functor.const (S Q)).obj Q.code where
  app P := by
    change (nativeCode Q).obj ((head (C Q)).obj P) ⟶ Q.code
    exact (nativeCode Q).map ((traversal (C := C Q)).app P) ≫
      targetCollapse Q ((tail (C Q)).obj P)
  naturality {P P'} f := by
    change (proj.map ((spanLabels Q).map f)).1 ≫ _ = _ ≫ 𝟙 _
    rw [spanLabels_projection, Category.comp_id]
    let F := nativeCode Q
    let a := (traversal (C := C Q)).app P
    let b := (traversal (C := C Q)).app P'
    let t := (tail (C Q)).map f
    let u := targetCollapse Q ((tail (C Q)).obj P)
    let v := targetCollapse Q ((tail (C Q)).obj P')
    change F.map ((head (C Q)).map f) ≫ F.map b ≫ v = F.map a ≫ u
    have h := congrArg F.map ((traversal (C := C Q)).naturality f)
    simp only [Functor.map_comp] at h
    have hw : F.map t ≫ v = u := congrArg (fun a ↦ a.hom) (CostructuredArrow.w t)
    rw [← Category.assoc, h, Category.assoc]
    rw [hw]

private abbrev spanParameter (P : S Q) :=
  JTGraphSpanFixedTargetData.parameterAt (W := W) (x := x) (y := y) (Q := Q) P

set_option maxHeartbeats 650000 in
private theorem spanParameter_map {P P' : S Q} (f : P ⟶ P') :
    ((proj.map ((spanLabels Q).map f)).1.map ⊗ₘ J.map ((time Q).map f)) ≫
      spanParameter Q P' = spanParameter Q P ≫ J.map (proj.map ((spanLabels Q).map f)).2 := by
  rw [spanLabels_projection]
  change ((((jointIndex Q).map f).1).map ⊗ₘ J.map ((jointIndex Q).map f).2) ≫
    spanParameter Q P' = spanParameter Q P ≫ J.map (degreeOperator ((tail (C Q)).map f).left)
  exact JTGraphSpanFixedTargetData.parameterAt_square
    (W := W) (x := x) (y := y) (Q := Q) (P := P) (P' := P') f

set_option maxHeartbeats 650000 in
/-- The data of every original span give one coherent reduced-cylinder family. -/
def spanFamily : Family Q (spanLabels Q) (time Q) where
  collapse := collapse Q
  parameter := spanParameter Q
  parameter_map f := spanParameter_map Q f
  raw P := JTGraphSpanFixedTargetData.rawAt (W := W) (x := x) (y := y) (Q := Q) P

/-- Evaluate the original simplex spans with all internal necklace operators. -/
def evaluate := JTParametrizedTargetFamilies.evaluate (spanFamily Q)

/-- The whole original cylinder diagram has the same operators as the native spans. -/
theorem cylinder_map {P P' : S Q} (f : P ⟶ P') :
    (JTParametrizedTargetFamilies.cylinders (L := spanLabels Q) (time := time Q)).map f =
      NecklaceCylinderJointDiagram.cylinderUnder.map ((jointIndex Q).map f) := by
  change NecklaceCylinderJointDiagram.cylinderUnder.map
    (show ((codes (spanLabels Q)).obj P, (time Q).obj P) ⟶
      ((codes (spanLabels Q)).obj P', (time Q).obj P') from
      ((proj.map ((spanLabels Q).map f)).1, (time Q).map f)) = _
  rw [spanLabels_projection]
  rfl

/-- The native and time operators give exactly the original cylinder diagram. -/
theorem cylinders_eq :
    JTParametrizedTargetFamilies.cylinders (L := spanLabels Q) (time := time Q) =
      jointIndex Q ⋙ NecklaceCylinderJointDiagram.cylinderUnder :=
  by
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro P P' f
    exact cylinder_map Q f

private abbrev tailCylinders := tail (C Q) ⋙ nativeCode Q ⋙ BoundaryNecklaceComma.necklaceUnder

private def augmentationUnder : NecklaceCylinderJointDiagram.cylinderUnder ⟶
    CategoryTheory.Prod.fst NecklaceCode SimplexCategory ⋙
      BoundaryNecklaceComma.necklaceUnder where
  app p := Under.homMk (NecklaceCylinderAugmentation.augmentation p.1 p.2)
    (NecklaceCylinderAugmentation.augmentation_boundary p.1 p.2)
  naturality _ _ f :=
    Under.UnderMorphism.ext (NecklaceCylinderJointDiagram.augmentation.naturality f)

/-- The cylinders of the literal span index, with the original native and time operators. -/
abbrev originalCylinders := jointIndex Q ⋙ NecklaceCylinderJointDiagram.cylinderUnder

/-- The native collapse follows the full original traversal to the final necklace. -/
def spanNativeCollapse : originalCylinders Q ⟶ tailCylinders Q :=
  Functor.whiskerLeft (jointIndex Q) augmentationUnder ≫
    Functor.whiskerRight (traversal (C := C Q))
      (nativeCode Q ⋙ BoundaryNecklaceComma.necklaceUnder)

/-- At a span the native collapse is the existing graph resolution collapse. -/
theorem spanNativeCollapse_app (P : S Q) : (spanNativeCollapse Q).app P =
    (nativeCollapse ((tail (C Q)).obj P)).app (parameter (Q := Q) P) :=
  Under.UnderMorphism.ext rfl

set_option maxHeartbeats 400000 in
/-- At a span the parameter lift is the existing pointwise two-leg lift. -/
theorem spanLift_app (P : S Q) :
    (JTParametrizedTargetFamilies.liftNatural (spanFamily Q)).app P =
      (JTGraphVariableTimeComparison.liftNatural ((tail (C Q)).obj P)).app
        (parameter (Q := Q) P) := by
  let U := (tail (C Q)).obj P
  let p : JTGraphVariableTimeIndex.Index U := parameter (Q := Q) P
  let i := (labels U).obj p
  let T := ((jointIndex Q).obj P).1
  let n := (time Q).obj P
  let F := spanFamily Q
  let graph := JTParametrizedTargetLiftTransport.graph (i := i) (F.parameter P)
  let c := F.collapse.app P
  let hr := F.raw P
  let u := JTCylinderOverTarget.lift W x y Q i T n graph c hr
  let v := (JTGraphVariableTimeComparison.liftNatural U).app p
  change u = v
  refine (IsPullback.of_hasPullback
    ((DecoratedCylinderNecklacePresentation.underCocone W x y).app i)
    (JTTargetCommaPullback.targetMap W x y Q)).hom_ext ?_ ?_
  · exact (JTCylinderOverTarget.lift_decorated W x y Q i T n graph c hr).trans
      (JTGraphVariableTimeComparison.lift_fst U p).symm
  · exact (JTCylinderOverTarget.lift_native W x y Q i T n graph c hr).trans
      (JTGraphVariableTimeComparison.lift_snd U p).symm

end
end DaggerModels.PartII.JTGraphSpanLift
