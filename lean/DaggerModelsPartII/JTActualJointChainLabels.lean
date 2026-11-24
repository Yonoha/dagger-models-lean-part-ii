import DaggerModelsPartII.JTActualJointChoiceChainGraph

/-! Restrict the actual decorated labels to every full coefficient-time chain. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

open CategoryTheory Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open DaggerModels DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTActualJointChainLabels

open JTParametrizedTargetFamilies (Family)
open JTTargetJointMarks (Joint)
open JTActualJointChoiceChainGraph (Index ordinals toOriginal graphCover graphProjection original X)
open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTRealizedLabelEndpoints (orderedLabel)
open JTNecklaceLabelRealization (realizedLabel)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time) (j : Joint Q.code)

private abbrev b := boundaryPoint W x y
private abbrev P := OrderedLabelElements.projection W (b (W := W) (x := x) (y := y))
private abbrev Y := OrderedLabelElements.labelPresheaf W (b (W := W) (x := x) (y := y))
private abbrev oldBase :=
  JTActualJointChoiceChainGraph.base F j ⋙ JTActualJointChoiceCover.projection F j ⋙
    JTExactlyMarkedSourceDiagram.base F j

/-- The unchanged actual decorated label at each full chain. -/
abbrev oldLabels : Index F j ⥤ OrderedLabelElements.Index W (b (W := W) (x := x) (y := y)) :=
  oldBase F j ⋙ L

private abbrev oldTag := oldLabels F j ⋙ P (W := W) (x := x) (y := y)
private abbrev chainTag :=
  ((oldTag F j ⋙ CategoryTheory.Prod.fst NecklaceCode SimplexCategory).prod'
    (ordinals F j))

private def oldOperator : chainTag F j ⟶ oldTag F j where
  app p := (𝟙 _, (toOriginal F j).app p)
  naturality _ _ f :=
    Prod.ext ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((toOriginal F j).naturality f)

private def restrictedLabel (p : Index F j) :
    (Y (W := W) (x := x) (y := y)).obj (op ((chainTag F j).obj p)) :=
  (Y (W := W) (x := x) (y := y)).map ((oldOperator F j).app p).op
    (OrderedLabelElements.label W (b (W := W) (x := x) (y := y)) ((oldLabels F j).obj p))

private theorem restrictedLabel_natural {p q : Index F j} (f : p ⟶ q) :
    (Y (W := W) (x := x) (y := y)).map ((chainTag F j).map f).op
      (restrictedLabel F j q) = restrictedLabel F j p := by
  unfold restrictedLabel
  rw [← FunctorToTypes.map_comp_apply, ← op_comp, (oldOperator F j).naturality f]
  rw [op_comp, FunctorToTypes.map_comp_apply]
  exact congrArg ((Y (W := W) (x := x) (y := y)).map ((oldOperator F j).app p).op)
    (((oldLabels F j).map f).unop.property)

/-- The actual original label restricted to every coefficient-time chain. -/
def chainLabels : Index F j ⥤ OrderedLabelElements.Index W
    (b (W := W) (x := x) (y := y)) where
  obj p := op ⟨op ((chainTag F j).obj p), restrictedLabel F j p⟩
  map f := Quiver.Hom.op ⟨((chainTag F j).map f).op, restrictedLabel_natural F j f⟩
  map_id p := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    exact congrArg Quiver.Hom.op ((chainTag F j).map_id p)
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    exact congrArg Quiver.Hom.op ((chainTag F j).map_comp f g)

/-- The chain label projects to its original label through the exact coefficient map. -/
def chainToOriginal : chainLabels F j ⟶ oldLabels F j where
  app p := Quiver.Hom.op ⟨((oldOperator F j).app p).op, rfl⟩
  naturality _ _ f := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    exact congrArg Quiver.Hom.op ((oldOperator F j).naturality f)

theorem chainToOriginal_projection (p : Index F j) :
    (P (W := W) (x := x) (y := y)).map ((chainToOriginal F j).app p) =
      (𝟙 _, (toOriginal F j).app p) := rfl



private abbrev T (p : Index F j) :=
  OrderedLabelElements.necklace W (b (W := W) (x := x) (y := y)) ((oldLabels F j).obj p)
private abbrev d (p : Index F j) :=
  OrderedLabelElements.degree W (b (W := W) (x := x) (y := y)) ((oldLabels F j).obj p)
private abbrev oldLabel (p : Index F j) :=
  OrderedLabelElements.label W (b (W := W) (x := x) (y := y)) ((oldLabels F j).obj p)
private abbrev newLabel (p : Index F j) :=
  OrderedLabelElements.label W (b (W := W) (x := x) (y := y)) ((chainLabels F j).obj p)

/-- The exact groupoid coefficient associated with the full chain. -/
abbrev chainParameter : graphCover F j ⟶ ordinals F j ⋙ J :=
  JTPrismChainGraphCover.parameter (X F j)
    (JTJointRelativeGraphFamily.originalParameter (original F j)) (toOriginal F j)

/-- The graph's original horizontal coordinate, unchanged by chain refinement. -/
abbrev horizontal (p : Index F j) :=
  ((graphProjection F j).app p) ≫
    fst (T F j p).toSSet (J.obj ((oldBase F j ⋙ time).obj p))

/-- The actual chain label has exactly the original raw value on the lifted graph. -/
theorem raw (p : Index F j) :
    lift (horizontal F j p) ((chainParameter F j).app p) ≫
      realizedLabel (T F j p).toSSet W ((ordinals F j).obj p)
        (orderedLabel W x y (T F j p) ((ordinals F j).obj p) (newLabel F j p)) =
    horizontal F j p ≫ ((original F j).collapse.app p).map ≫ Q.map := by
  let τ := chainParameter F j
  have h := ((chainToOriginal F j).app p).unop.property
  have hv := NatTrans.congr_app
    (JTActualJointChoiceChainGraph.graphParameter_projection F j) p
  change τ.app p ≫ J.map ((toOriginal F j).app p) =
    (graphProjection F j).app p ≫ (original F j).parameter p at hv
  change lift (horizontal F j p) (τ.app p) ≫ _ = _
  have hr := JTPrismChainGraphCover.realize_on_common_chain
    ((toOriginal F j).app p) (𝟙 ((ordinals F j).obj p))
    (horizontal F j p) (τ.app p) (oldLabel F j p) (newLabel F j p) (by
      let O := OrderedNecklaceLabelDiagram.orderedNecklaceLabels W
        (b (W := W) (x := x) (y := y))
      change (O.obj (op (T F j p))).map ((toOriginal F j).app p).op
          (((O.map (𝟙 (T F j p)).op).app (op (d F j p))) (oldLabel F j p)) =
        newLabel F j p at h
      rw [op_id, O.map_id] at h
      simpa using h)
  change lift (horizontal F j p) (τ.app p ≫ J.map (𝟙 _)) ≫ _ = _ at hr
  rw [J.map_id] at hr
  change lift (horizontal F j p) (τ.app p) ≫ _ = _ at hr
  refine hr.trans ?_
  rw [hv]
  have ht := JTParametrizedTargetFamilies.rawProduct (original F j) p
  change lift ((graphProjection F j).app p ≫ fst _ _)
       ((graphProjection F j).app p ≫ (original F j).parameter p) ≫ _ = _
  rw [← CartesianMonoidalCategory.comp_lift, Category.assoc]
  exact (congrArg ((graphProjection F j).app p ≫ ·) ht).trans
    (Category.assoc _ _ _).symm

end
end DaggerModels.PartII.JTActualJointChainLabels
