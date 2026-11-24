import DaggerModelsPartII.JTExactlyMarkedSourceDiagram
import DaggerModelsPartII.JTActualJointCutCoefficientTransport

/-!
The literal left and right cuts on the actual exactly marked source category.
Native functor laws and coefficient equations apply the existing cut-map and
coefficient-transport results. No corrected edge or new coefficient is introduced.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 150000

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTExactlyMarkedCutDiagrams

open JTParametrizedTargetFamilies (Family codes)
open JTTargetJointMarks (Joint)
open JTProjectiveOrderedFiberComparison (row)
open TripleBeadEndpointLabel (labels)
open DaggerOriginalProductGadget

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev pre (W : Source) {X Y : SSet.{0}} (g : X ⟶ Y) :=
  diagramMappingPrecomp (ReversalDiscreteFreeColimits.discreteFree.map g) W

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time) (j : Joint Q.code)

private abbrev I := JTExactlyMarkedSourceDiagram.Index F j
private abbrev K := JTExactlyMarkedSourceDiagram.degrees F j

/-- The actual left cut, along every exactly cut-preserving original arrow. -/
def leftNative : I F j ⥤ NecklaceCode where
  obj a := cutLeft ((codes L).obj a.1) a.2.val
  map {a b} g := cutLeftHom ((codes L).map g.val) a.2.val b.2.val
    (JTExactlyMarkedSourceDiagram.cut_map F j g)
  map_id a := by
    change cutLeftHom ((codes L).map (𝟙 a.1)) a.2.val a.2.val _ = _
    simpa only [(codes L).map_id] using
      cutLeftHom_id ((codes L).obj a.1) a.2.val
  map_comp {a b c} g h := by
    change cutLeftHom ((codes L).map (g.val ≫ h.val)) a.2.val c.2.val _ = _
    simpa only [(codes L).map_comp] using
      cutLeftHom_comp ((codes L).map g.val) ((codes L).map h.val)
        a.2.val b.2.val c.2.val (JTExactlyMarkedSourceDiagram.cut_map F j g)
        (JTExactlyMarkedSourceDiagram.cut_map F j h)

/-- The actual right cut, with the identical original-arrow indexing. -/
def rightNative : I F j ⥤ NecklaceCode where
  obj a := cutRight ((codes L).obj a.1) a.2.val
  map {a b} g := cutRightHom ((codes L).map g.val) a.2.val b.2.val
    (JTExactlyMarkedSourceDiagram.cut_map F j g)
  map_id a := by
    change cutRightHom ((codes L).map (𝟙 a.1)) a.2.val a.2.val _ = _
    simpa only [(codes L).map_id] using
      cutRightHom_id ((codes L).obj a.1) a.2.val
  map_comp {a b c} g h := by
    change cutRightHom ((codes L).map (g.val ≫ h.val)) a.2.val c.2.val _ = _
    simpa only [(codes L).map_comp] using
      cutRightHom_comp ((codes L).map g.val) ((codes L).map h.val)
        a.2.val b.2.val c.2.val (JTExactlyMarkedSourceDiagram.cut_map F j g)
        (JTExactlyMarkedSourceDiagram.cut_map F j h)

/-- Restrict the complete original coefficient to the literal left cut. -/
abbrev leftCoefficient (a : I F j) :
    std.obj ((K F j).obj a) ⟶ labels W ((leftNative F j).obj a) :=
  JTActualJointCutPrism.leftCoefficient (L := L) a.1 a.2.val

/-- Restrict the same complete original coefficient to the literal right cut. -/
abbrev rightCoefficient (a : I F j) :
    std.obj ((K F j).obj a) ⟶ labels W ((rightNative F j).obj a) :=
  JTActualJointCutPrism.rightCoefficient (L := L) a.1 a.2.val

/-- Full coefficient transport along every actual exact-cut source arrow. -/
theorem left_natural {a b : I F j} (g : a ⟶ b) :
    leftCoefficient F j a = std.map ((K F j).map g) ≫
      leftCoefficient F j b ≫ pre W ((leftNative F j).map g).map :=
  JTActualJointCutCoefficientTransport.leftCoefficient_map (L := L) g.val
    a.2.val b.2.val (JTExactlyMarkedSourceDiagram.cut_map F j g)

/-- The right coefficients retain the same complete mixed operator equation. -/
theorem right_natural {a b : I F j} (g : a ⟶ b) :
    rightCoefficient F j a = std.map ((K F j).map g) ≫
      rightCoefficient F j b ≫ pre W ((rightNative F j).map g).map :=
  JTActualJointCutCoefficientTransport.rightCoefficient_map (L := L) g.val
    a.2.val b.2.val (JTExactlyMarkedSourceDiagram.cut_map F j g)

end
end DaggerModels.PartII.JTExactlyMarkedCutDiagrams
