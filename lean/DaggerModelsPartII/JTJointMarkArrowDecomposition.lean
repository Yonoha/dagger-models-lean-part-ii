import DaggerModelsPartII.JTTargetJointMarks

/-! Horizontal transport followed by vertical movement of native joint marks. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory DaggerModels DaggerChosenRigidificationNecklace
open NecklaceCode

namespace DaggerModels.PartII.JTJointMarkArrowDecomposition

noncomputable section

variable {B : Type} [SmallCategory B] (U : NecklaceCode)
    (T : B ⥤ Over U)

private abbrev D := T ⋙ JTTargetJointMarks.nativeDiagram U
private abbrev Marked := Grothendieck (D U T)

/-- The fiber part of a marked arrow, regarded as a vertical arrow after
transport along its underlying over-target map. -/
def vertical {X Y : Marked U T} (f : X ⟶ Y) :
    X.transport f.base ⟶ Y :=
  ⟨𝟙 Y.base, eqToHom (by simp) ≫ f.fiber⟩

theorem vertical_base {X Y : Marked U T} (f : X ⟶ Y) :
    (vertical U T f).base = 𝟙 Y.base := rfl

/-- Every marked arrow factors into strict base transport and a vertical
coordinatewise movement of the cut. -/
theorem factor {X Y : Marked U T} (f : X ⟶ Y) :
    Grothendieck.toTransport X f.base ≫ vertical U T f = f := by
  apply Grothendieck.ext
  · simp [vertical]
  · simp [vertical]

def mark (X : Marked U T) :
    JTTargetJointMarks.Marks ((T.obj X.base).hom) := X.fiber

def transportedMark {X Y : Marked U T} (f : X ⟶ Y) :
    JTTargetJointMarks.Marks ((T.obj Y.base).hom) :=
  ((D U T).map f.base).toFunctor.obj X.fiber

/-- The vertical component only moves the transported cuts upward. -/
theorem transported_le {X Y : Marked U T} (f : X ⟶ Y)
    (j : JTTargetJointMarks.Joint U) :
    transportedMark U T f j ≤ mark U T Y j := by
  have h : transportedMark U T f ⟶ mark U T Y := f.fiber
  exact (leOfHom h) j

/-- The transported cut is the source cut's image under the base map. -/
theorem transportedMark_vertex {X Y : Marked U T} (f : X ⟶ Y)
    (j : JTTargetJointMarks.Joint U) :
    (transportedMark U T f j).val =
      orderMap (T.map f.base).left.map ((mark U T X j).val) := rfl

/-- The actual source interval endpoint maps below the moved endpoint. -/
theorem cut_image_le {X Y : Marked U T} (f : X ⟶ Y)
    (j : JTTargetJointMarks.Joint U) :
    orderMap (T.map f.base).left.map ((mark U T X j).val) ≤
      (mark U T Y j).val := by
  have h := transported_le U T f j
  change (transportedMark U T f j).val ≤ (mark U T Y j).val at h
  rw [transportedMark_vertex] at h
  exact h

end

end DaggerModels.PartII.JTJointMarkArrowDecomposition
