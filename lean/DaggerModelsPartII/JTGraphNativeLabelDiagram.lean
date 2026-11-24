import DaggerModelsPartII.JTGraphInterpolatedCollapseOriginal

/-! The exact ordered label pulled back along every native collapse. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphNativeLabelDiagram

open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphLiftTransport
open JTGraphInterpolatedRaw (index)
open JTGraphInterpolatedCollapseOriginal (indexCollapse indexCollapse_operator)
open JTCommaGraphPredecessor (augmentationCode)
open JTGraphToPresentationArrow (pulledLabel)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable (U : TargetComma Q)

private abbrev NativeSlice := Over U.left.fiber.left
private abbrev Labels := OrderedNecklaceLabelDiagram.orderedNecklaceLabels W (boundaryPoint W x y)

private theorem pulledLabel_restrict {P P' : NativeSlice U} (f : P ⟶ P') :
    ((Labels (W := W) (x := x) (y := y)).map f.left.op).app (op (degree U.left))
      (pulledLabel U.left P'.left (P'.hom ≫ augmentationCode U.left)) =
    pulledLabel U.left P.left (P.hom ≫ augmentationCode U.left) := by
  let L := Labels (W := W) (x := x) (y := y)
  let b := op (degree U.left)
  let z := OrderedLabelElements.label W (boundaryPoint W x y) U.left.base
  change (L.map f.left.op).app b
      ((L.map (P'.hom ≫ augmentationCode U.left).op).app b z) =
    (L.map (P.hom ≫ augmentationCode U.left).op).app b z
  have h : f.left ≫ (P'.hom ≫ augmentationCode U.left) = P.hom ≫ augmentationCode U.left := by
    rw [← Category.assoc, Over.w f]
  have hL : L.map (P'.hom ≫ augmentationCode U.left).op ≫ L.map f.left.op =
      L.map (P.hom ≫ augmentationCode U.left).op := by
    rw [← L.map_comp, ← op_comp, h]
  exact congrArg (fun a ↦ a.app b z) hL

private def labelMap {P P' : NativeSlice U} (f : P ⟶ P') :
    index U P.hom ⟶ index U P'.hom := by
  let g : (P.left, degree U.left) ⟶ (P'.left, degree U.left) := (f.left, 𝟙 _)
  refine (CategoryOfElements.homMk (index U P'.hom).unop (index U P.hom).unop g.op ?_).op
  change ((Labels (W := W) (x := x) (y := y)).obj (op P.left)).map (𝟙 _).op _ = _
  rw [op_id, ((Labels (W := W) (x := x) (y := y)).obj (op P.left)).map_id]
  exact pulledLabel_restrict U f

private theorem label_ext {a b : DecoratedNecklaceHomDiagram.Index W x y} {f g : a ⟶ b}
    (h : (projection (W := W) (x := x) (y := y)).map f =
      (projection (W := W) (x := x) (y := y)).map g) : f = g := by
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  exact congrArg (fun p ↦ p.op) h

/-- The original fixed label is pulled back functorially along all native source maps. -/
def diagram : NativeSlice U ⥤ DecoratedNecklaceHomDiagram.Index W x y where
  obj P := index U P.hom
  map := labelMap U
  map_id P := by
    apply label_ext
    rw [(projection (W := W) (x := x) (y := y)).map_id]
    rfl
  map_comp {P P' P''} f g := by
    apply label_ext
    rw [(projection (W := W) (x := x) (y := y)).map_comp]
    change (f.left ≫ g.left, 𝟙 (degree U.left)) =
      (f.left ≫ g.left, 𝟙 (degree U.left) ≫ 𝟙 (degree U.left))
    rw [Category.id_comp]

theorem diagram_map {P P' : NativeSlice U} (f : P ⟶ P') :
    (projection (W := W) (x := x) (y := y)).map ((diagram U).map f) =
      (f.left, 𝟙 (degree U.left)) := rfl

private def toOriginalApp (P : NativeSlice U) : (diagram U).obj P ⟶ U.left.base := by
  let L := Labels (W := W) (x := x) (y := y)
  let g : (P.left, degree U.left) ⟶ (code U.left, degree U.left) :=
    (P.hom ≫ augmentationCode U.left, 𝟙 _)
  refine (CategoryOfElements.homMk U.left.base.unop (index U P.hom).unop g.op ?_).op
  change (L.obj (op P.left)).map (𝟙 _).op _ = _
  rw [op_id, (L.obj (op P.left)).map_id]
  rfl

/-- The decorated comparison to the original label is natural in the native source. -/
def toOriginal : diagram U ⟶ (Functor.const _).obj U.left.base where
  app := toOriginalApp U
  naturality {P P'} f := by
    apply label_ext
    rw [(projection (W := W) (x := x) (y := y)).map_comp,
      (projection (W := W) (x := x) (y := y)).map_comp]
    let H := projection (W := W) (x := x) (y := y)
    change H.map ((diagram U).map f) ≫ H.map (toOriginalApp U P') =
      H.map (toOriginalApp U P) ≫ H.map (𝟙 U.left.base)
    rw [H.map_id]
    refine Eq.trans ?_ (Category.comp_id _).symm
    change (f.left ≫ (P'.hom ≫ augmentationCode U.left),
        𝟙 (degree U.left) ≫ 𝟙 (degree U.left)) =
      (P.hom ≫ augmentationCode U.left, 𝟙 (degree U.left))
    exact Prod.ext (by rw [← Category.assoc, Over.w f]) (Category.id_comp _)

/-- The variable-label comparison agrees with the checked pointwise collapse. -/
theorem toOriginal_app (P : NativeSlice U) {n : SimplexCategory}
    (D : Fin (n.len + 1) → GraphLift U.left P.left) (hD : ∀ i, (D i).collapse = P.hom) :
    (toOriginal U).app P = indexCollapse P.hom D hD := by
  apply label_ext
  rw [indexCollapse_operator]
  rfl

end
end DaggerModels.PartII.JTGraphNativeLabelDiagram
