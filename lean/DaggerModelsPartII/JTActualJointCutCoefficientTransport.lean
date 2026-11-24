import DaggerModelsPartII.JTActualJointCutPrism
import DaggerModelsPartII.JTActualJointSideNativeTransport
import DaggerModelsPartII.JTOrderedLabelWedge
import OriginalCutMapLaws

/-! Exact coefficient transport along cut-preserving arrows of an actual family. -/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTActualJointCutCoefficientTransport

open ReversalDiscreteFreeColimits
open TripleBeadEndpointLabel (labels)
open JTParametrizedTargetFamilies (Family codes)
open DaggerOriginalProductGadget (cutLeftHom cutRightHom cutLeftHom_fac cutRightHom_fac)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev free := discreteFree.{0}
private abbrev pre (W : Source) {X Y : SSet.{0}} (i : X ⟶ Y) :=
  diagramMappingPrecomp (free.map i) W

variable {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {A : Type} [SmallCategory A]
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) {a b : A} (α : a ⟶ b)

private abbrev T (c : A) := (codes L).obj c
private abbrev k := JTJointRelativeGraphFamily.coefficient (L := L)
private abbrev g := (codes L).map α
private abbrev r := k (L := L) (A := A).map α

/-- The original full coefficient follows the native and ordinal operators of `L.map α`. -/
private theorem originalCoefficient_map :
    JTActualJointCutPrism.originalCoefficient (L := L) a =
      std.map (r (L := L) α) ≫
        JTActualJointCutPrism.originalCoefficient (L := L) b ≫
          pre W (g (L := L) α).map := by
  let B := OrderedNecklaceVertexPoints.boundaryPoint W x y
  let P := OrderedLabelElements.projection W B
  have h := JTOrderedLabelWedge.coefficient_of_indexHom
    (W := W) (x := x) (y := y)
    (OrderedLabelElements.label W B (L.obj a))
    (OrderedLabelElements.label W B (L.obj b))
    (g (L := L) α) (r (L := L) α) (L.map α)
    (show P.map (L.map α) = (g (L := L) α, r (L := L) α) from rfl)
  simpa only [JTActualJointCutPrism.originalCoefficient,
    JTActualSourceJointSupport.oldCoefficient] using h

variable (v : Fin ((T (L := L) a).len + 1))
variable (v' : Fin ((T (L := L) b).len + 1))
variable (hv : orderMap (g (L := L) α).map v = v')

/-- The literal left-cut coefficient is natural along a cut-preserving source arrow. -/
theorem leftCoefficient_map :
    JTActualJointCutPrism.leftCoefficient (L := L) a v =
      std.map (r (L := L) α) ≫
        JTActualJointCutPrism.leftCoefficient (L := L) b v' ≫
          pre W (cutLeftHom (g (L := L) α) v v' hv).map := by
  rw [JTActualJointCutPrism.leftCoefficient,
    JTActualJointCutPrism.leftCoefficient,
    originalCoefficient_map (L := L) α]
  simp only [Category.assoc, ← diagramMappingPrecomp_comp,
    ← free.map_comp, cutLeftHom_fac]

/-- The literal right-cut coefficient is natural along a cut-preserving source arrow. -/
theorem rightCoefficient_map :
    JTActualJointCutPrism.rightCoefficient (L := L) a v =
      std.map (r (L := L) α) ≫
        JTActualJointCutPrism.rightCoefficient (L := L) b v' ≫
          pre W (cutRightHom (g (L := L) α) v v' hv).map := by
  rw [JTActualJointCutPrism.rightCoefficient,
    JTActualJointCutPrism.rightCoefficient,
    originalCoefficient_map (L := L) α]
  simp only [Category.assoc, ← diagramMappingPrecomp_comp,
    ← free.map_comp, cutRightHom_fac]

end
end DaggerModels.PartII.JTActualJointCutCoefficientTransport
