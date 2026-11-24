import DaggerModelsPartII.JTJointCutSubdivision
import DaggerModelsPartII.JTNativePulledCutComparison

/-!
# A common subdivision compares the two original cut evaluations

At a fixed object of the original diagram, pull the entire ordered label
and time graph back to the three pieces and to each of the two cuts. The
two natural transformations live in the original fixed-target comma.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTActualJointCutSubdivisionEvaluation

open JTParametrizedTargetFamilies (Family codes)
open JTJointCutSubdivision (cut common toEarlier toLater)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

private def toCode {T : NecklaceCode} (P : NecklacesOver (toSSet.{0} T)
    (T.verticesEquiv.symm (ULift.up 0)) (T.verticesEquiv.symm (ULift.up (Fin.last T.len)))) :
    P.code ⟶ T where
  map := P.map
  first := P.first
  last := P.last

variable {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {A : Type} [SmallCategory A]
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (a : A)
private abbrev T := (codes L).obj a
variable (v w : Fin ((T (L := L) a).len + 1)) (h : v ≤ w)

private abbrev e := toCode (cut (T (L := L) a) v)
private abbrev l := toCode (cut (T (L := L) a) w)
private abbrev b := toCode (common (T (L := L) a) v w h)

private theorem earlier_fac :
    (toEarlier (T (L := L) a) v w h).hom ≫ e (L := L) a v = b (L := L) a v w h :=
  NecklaceCode.Hom.ext (toEarlier (T (L := L) a) v w h).w

private theorem later_fac :
    (toLater (T (L := L) a) v w h).hom ≫ l (L := L) a w = b (L := L) a v w h :=
  NecklaceCode.Hom.ext (toLater (T (L := L) a) v w h).w

/-- Evaluate the entire three-piece subdivision using the original graph. -/
def commonEvaluation :=
  JTNativePulledCutComparison.evaluation (L.obj a) (time.obj a) (F.collapse.app a)
    (F.parameter a) (F.raw a) (b (L := L) a v w h)

/-- The same graph restricted to the full two-piece subdivision at a given cut. -/
def cutEvaluation :=
  JTNativePulledCutComparison.evaluation (L.obj a) (time.obj a) (F.collapse.app a)
    (F.parameter a) (F.raw a) (e (L := L) a v)

/-- A comparison from the common subdivision to the earlier cut in the actual original comma. -/
def earlierComparison :=
  JTNativePulledCutComparison.compare (L.obj a) (time.obj a) (F.collapse.app a)
    (F.parameter a) (F.raw a) (b (L := L) a v w h) (e (L := L) a v)
    (toEarlier (T (L := L) a) v w h).hom (earlier_fac (L := L) a v w h)

/-- A comparison from the common subdivision to the later cut in the same original comma. -/
def laterComparison :=
  JTNativePulledCutComparison.compare (L.obj a) (time.obj a) (F.collapse.app a)
    (F.parameter a) (F.raw a) (b (L := L) a v w h) (l (L := L) a w)
    (toLater (T (L := L) a) v w h).hom (later_fac (L := L) a v w h)

end
end DaggerModels.PartII.JTActualJointCutSubdivisionEvaluation
