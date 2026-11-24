import DaggerModelsPartII.JTExactlyMarkedSourceDiagram

/-! The original source diagram with two ordered cuts above one target joint. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTJointPairSourceDiagram

open JTParametrizedTargetFamilies (Family codes)
open JTTargetJointMarks (Joint)
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time) (j : Joint Q.code)

/-- Two ordered original source vertices lying above the same target joint. -/
structure Pair (a : A) where
  left : (JTExactlyMarkedSourceDiagram.vertices F j).obj a
  right : (JTExactlyMarkedSourceDiagram.vertices F j).obj a
  le : left.val ≤ right.val

private def transport {a b : A} (f : a ⟶ b) (p : Pair F j a) : Pair F j b where
  left := (JTExactlyMarkedSourceDiagram.vertices F j).map f p.left
  right := (JTExactlyMarkedSourceDiagram.vertices F j).map f p.right
  le := (orderMap ((codes L).map f).map).monotone p.le

/-- Both original cuts are transported simultaneously by every source arrow. -/
def pairs : A ⥤ Type where
  obj := Pair F j
  map := transport F j
  map_id a := by
    funext p
    cases p
    simp [transport]
  map_comp {a b c} f g := by
    funext p
    cases p
    simp [transport]

/-- The category of source objects with two exactly transported ordered cuts. -/
abbrev Index := (pairs F j).Elements

/-- Retain the original source object and arrow. -/
abbrev base : Index F j ⥤ A := CategoryOfElements.π (pairs F j)

private def leftProjection : pairs F j ⟶ JTExactlyMarkedSourceDiagram.vertices F j where
  app _ p := p.left
  naturality _ _ _ := rfl

private def rightProjection : pairs F j ⟶ JTExactlyMarkedSourceDiagram.vertices F j where
  app _ p := p.right
  naturality _ _ _ := rfl

/-- Forget the later cut, preserving its exact source-arrow transport. -/
abbrev leftCut : Index F j ⥤ JTExactlyMarkedSourceDiagram.Index F j :=
  CategoryOfElements.map (leftProjection F j)

/-- Forget the earlier cut, preserving its exact source-arrow transport. -/
abbrev rightCut : Index F j ⥤ JTExactlyMarkedSourceDiagram.Index F j :=
  CategoryOfElements.map (rightProjection F j)

theorem left_map {p q : Index F j} (f : p ⟶ q) :
    orderMap ((codes L).map f.val).map p.2.left.val = q.2.left.val :=
  JTExactlyMarkedSourceDiagram.cut_map F j ((leftCut F j).map f)

theorem right_map {p q : Index F j} (f : p ⟶ q) :
    orderMap ((codes L).map f.val).map p.2.right.val = q.2.right.val :=
  JTExactlyMarkedSourceDiagram.cut_map F j ((rightCut F j).map f)

end
end DaggerModels.PartII.JTJointPairSourceDiagram
