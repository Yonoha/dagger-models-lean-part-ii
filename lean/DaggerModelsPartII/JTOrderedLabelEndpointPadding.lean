import DaggerModelsPartII.DecoratedNecklaceHomDiagram
import DaggerModelsPartII.JTNativeEndpointPadding

/-! Endpoint padding on the actual ordered-label category of elements. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTOrderedLabelEndpointPadding

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

variable (W : Source)
  (x y : (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌))

private abbrev I := DecoratedNecklaceHomDiagram.Index W x y
private abbrev P := OrderedLabelElements.labelPresheaf W
  (OrderedNecklaceVertexPoints.boundaryPoint W x y)
private abbrev pr := OrderedLabelElements.projection W
  (OrderedNecklaceVertexPoints.boundaryPoint W x y)

private def paddedObject (i : I W x y) : I W x y :=
  op ((P W x y).elementsMk
    (op (JTNativeEndpointPadding.pad.obj (((pr W x y).obj i).1),
      ((pr W x y).obj i).2))
    ((P W x y).map
      (Quiver.Hom.op ((JTNativeEndpointPadding.collapse.app (((pr W x y).obj i).1),
        𝟙 (((pr W x y).obj i).2)) :
          (JTNativeEndpointPadding.pad.obj (((pr W x y).obj i).1),
            ((pr W x y).obj i).2) ⟶ (pr W x y).obj i)) i.unop.2))

private def paddedMap {i j : I W x y} (f : i ⟶ j) :
    paddedObject W x y i ⟶ paddedObject W x y j := by
  let a := (pr W x y).map f
  let c (i : I W x y) :
      (JTNativeEndpointPadding.pad.obj (((pr W x y).obj i).1),
        ((pr W x y).obj i).2) ⟶ (pr W x y).obj i :=
    (JTNativeEndpointPadding.collapse.app (((pr W x y).obj i).1),
      𝟙 (((pr W x y).obj i).2))
  let b :
      (JTNativeEndpointPadding.pad.obj (((pr W x y).obj i).1),
        ((pr W x y).obj i).2) ⟶
      (JTNativeEndpointPadding.pad.obj (((pr W x y).obj j).1),
        ((pr W x y).obj j).2) :=
    (JTNativeEndpointPadding.pad.map a.1, a.2)
  have hbc : b ≫ c j = c i ≫ a := by
    apply CategoryTheory.Prod.hom_ext
    · exact JTNativeEndpointPadding.collapse.naturality a.1
    · simp [c, b]
  refine (CategoryOfElements.homMk (paddedObject W x y j).unop
    (paddedObject W x y i).unop b.op ?_).op
  change (P W x y).map b.op ((P W x y).map (c j).op j.unop.2) =
    (P W x y).map (c i).op i.unop.2
  calc
    _ = (P W x y).map (b ≫ c j).op j.unop.2 := by
      rw [op_comp, (P W x y).map_comp]
      rfl
    _ = (P W x y).map (c i ≫ a).op j.unop.2 := by rw [hbc]
    _ = (P W x y).map (c i).op ((P W x y).map a.op j.unop.2) := by
      rw [op_comp, (P W x y).map_comp]
      rfl
    _ = _ := by rw [show (P W x y).map a.op j.unop.2 = i.unop.2 from f.unop.property]

/-- Pad the native necklace and pull its ordered label back along the collapse. -/
def pad : I W x y ⥤ I W x y where
  obj := paddedObject W x y
  map := paddedMap W x y
  map_id i := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    have h :
      (JTNativeEndpointPadding.pad.map (𝟙 (((pr W x y).obj i).1)),
        𝟙 (((pr W x y).obj i).2)) =
      (𝟙 (JTNativeEndpointPadding.pad.obj (((pr W x y).obj i).1)),
        𝟙 (((pr W x y).obj i).2)) := by
      rw [JTNativeEndpointPadding.pad.map_id]
    exact congrArg
      (fun q : (JTNativeEndpointPadding.pad.obj (((pr W x y).obj i).1),
        ((pr W x y).obj i).2) ⟶
        (JTNativeEndpointPadding.pad.obj (((pr W x y).obj i).1),
          ((pr W x y).obj i).2) ↦ q.op) h
  map_comp {i j k} f g := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    have h : (JTNativeEndpointPadding.pad.map ((pr W x y).map (f ≫ g)).1,
      ((pr W x y).map (f ≫ g)).2) =
      (JTNativeEndpointPadding.pad.map ((pr W x y).map f).1 ≫
        JTNativeEndpointPadding.pad.map ((pr W x y).map g).1,
        ((pr W x y).map f).2 ≫ ((pr W x y).map g).2) := by
      rw [(pr W x y).map_comp]
      simp
    exact congrArg
      (fun q : (JTNativeEndpointPadding.pad.obj (((pr W x y).obj i).1),
        ((pr W x y).obj i).2) ⟶
        (JTNativeEndpointPadding.pad.obj (((pr W x y).obj k).1),
          ((pr W x y).obj k).2) ↦ q.op) h

/-- Collapse padded decorated labels to their original labels. -/
def collapse : pad W x y ⟶ 𝟭 (I W x y) where
  app i := by
    let c :
        (JTNativeEndpointPadding.pad.obj (((pr W x y).obj i).1),
          ((pr W x y).obj i).2) ⟶ (pr W x y).obj i :=
      (JTNativeEndpointPadding.collapse.app (((pr W x y).obj i).1),
        𝟙 (((pr W x y).obj i).2))
    refine (CategoryOfElements.homMk i.unop (paddedObject W x y i).unop c.op ?_).op
    dsimp [c, paddedObject]
  naturality := by
    intro i j f
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    have h :
      (JTNativeEndpointPadding.pad.map ((pr W x y).map f).1 ≫
        JTNativeEndpointPadding.collapse.app (((pr W x y).obj j).1),
        ((pr W x y).map f).2 ≫ 𝟙 (((pr W x y).obj j).2)) =
      (JTNativeEndpointPadding.collapse.app (((pr W x y).obj i).1) ≫
        ((pr W x y).map f).1,
        𝟙 (((pr W x y).obj i).2) ≫ ((pr W x y).map f).2) :=
      Prod.ext (JTNativeEndpointPadding.collapse.naturality ((pr W x y).map f).1)
        (by simp)
    exact congrArg
      (fun q : (JTNativeEndpointPadding.pad.obj (((pr W x y).obj i).1),
        ((pr W x y).obj i).2) ⟶ (pr W x y).obj j ↦ q.op) h

@[simp] theorem projection_obj (i : I W x y) :
    (pr W x y).obj ((pad W x y).obj i) =
      (JTNativeEndpointPadding.pad.obj (((pr W x y).obj i).1),
        ((pr W x y).obj i).2) := rfl

@[simp] theorem projection_map {i j : I W x y} (f : i ⟶ j) :
    (pr W x y).map ((pad W x y).map f) =
      (JTNativeEndpointPadding.pad.map ((pr W x y).map f).1,
        ((pr W x y).map f).2) := rfl

@[simp] theorem projection_collapse (i : I W x y) :
    (pr W x y).map ((collapse W x y).app i) =
      (JTNativeEndpointPadding.collapse.app (((pr W x y).obj i).1), 𝟙 _) := rfl

end

end DaggerModels.PartII.JTOrderedLabelEndpointPadding
