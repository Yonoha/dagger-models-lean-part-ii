import DaggerModelsPartII.JTActualObjectLiftedFamily
import DaggerModelsPartII.JTActualJointCutSubdivisionEvaluation
import DaggerModelsPartII.JTActualSpanMarkedCover
import DaggerModelsPartII.JTGraphCylinderFiberDiagram

/-!
An actual objectwise vertical cut comparison in the fixed original target.
`JTActualObjectLiftedFamily.family` supplies the full internal coefficient and
time graph; `JTJointCutSubdivision` supplies the common native subdivision;
`JTActualJointCutSubdivisionEvaluation` supplies both complete comparisons.
The source functors between internal-necklace fibers are kept explicit.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTActualMarkedVerticalCutComparison

open JTGraphFactoredPresentation (TargetComma)
open JTProjectiveOrderedFiberComparison (row)
open JTTargetJointMarks (Joint Marks)
open JTActualObjectLiftedFamily (source traversal family)
open JTJointCutSubdivision (cut common toEarlier toLater)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev unit : Discrete PUnit := ⟨PUnit.unit⟩

variable {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable (V : TargetComma Q) (m n : Marks V.hom.hom) (hm : m ≤ n)
variable (s : JTInternalTraversalLifts.Lift (traversal V)) (j : Joint Q.code)

/-- The two actual vertices over the target joint. -/
abbrev earlierCut : Fin ((source V).len + 1) := (m j).val
abbrev laterCut : Fin ((source V).len + 1) := (n j).val

/-- The vertical mark arrow supplies the actual ordered cut relation. -/
theorem cut_le (hm' : m ≤ n) : earlierCut V m j ≤ laterCut V n j := hm' j

/-- The first source cut is above the fixed original target joint. -/
theorem earlier_joint :
    orderMap ((family V s).collapse.app unit).map (earlierCut V m j) = j.val := by
  rw [JTActualObjectLiftedFamily.family_nativeCollapse]
  exact (m j).property

/-- The second source cut is above the same target joint. -/
theorem later_joint :
    orderMap ((family V s).collapse.app unit).map (laterCut V n j) = j.val := by
  rw [JTActualObjectLiftedFamily.family_nativeCollapse]
  exact (n j).property

private abbrev T := source V
private abbrev v := earlierCut V m j
private abbrev w := laterCut V n j
private abbrev h := hm j

/-- The common three-piece internal necklace, with its original endpoints. -/
abbrev commonCode := (common (T V) (v V m j) (w V n j) (h V m n hm j)).code

/-- The earlier two-piece internal necklace. -/
abbrev earlierCode := (cut (T V) (v V m j)).code

/-- The later two-piece internal necklace. -/
abbrev laterCode := (cut (T V) (w V n j)).code

/-- The complete internal-necklace fiber at degree zero. -/
private abbrev Fiber (C : NecklaceCode) := JTGraphInterpolatedComparison.Fiber C ⦋0⦌

/-- The exact common-source map to the earlier internal-necklace fiber. -/
def toEarlierFiber : Fiber (commonCode V m n hm j) ⥤
    Fiber (earlierCode V m j) :=
  JTGraphCylinderFiberDiagram.joint
    (toEarlier (T V) (v V m j) (w V n j) (h V m n hm j)).hom (𝟙 ⦋0⦌)

/-- The exact common-source map to the later internal-necklace fiber. -/
def toLaterFiber : Fiber (commonCode V m n hm j) ⥤
    Fiber (laterCode V n j) :=
  JTGraphCylinderFiberDiagram.joint
    (toLater (T V) (v V m j) (w V n j) (h V m n hm j)).hom (𝟙 ⦋0⦌)

/-- Evaluate every internal necklace of the full common subdivision in `Q`. -/
abbrev commonEvaluation : Fiber (commonCode V m n hm j) ⥤ TargetComma Q :=
  JTActualJointCutSubdivisionEvaluation.commonEvaluation (family V s) unit
    (v V m j) (w V n j) (h V m n hm j)

/-- The earlier full two-piece evaluation in the same original target. -/
abbrev earlierEvaluation : Fiber (earlierCode V m j) ⥤ TargetComma Q :=
  JTActualJointCutSubdivisionEvaluation.cutEvaluation (family V s) unit (v V m j)

/-- The later full two-piece evaluation in the same original target. -/
abbrev laterEvaluation : Fiber (laterCode V n j) ⥤ TargetComma Q :=
  JTActualJointCutSubdivisionEvaluation.cutEvaluation (family V s) unit (w V n j)

/-- First complete comparison, with its internal-necklace domain map visible. -/
def earlierComparison : commonEvaluation V m n hm s j ⟶
    toEarlierFiber V m n hm j ⋙ earlierEvaluation V m s j :=
  JTActualJointCutSubdivisionEvaluation.earlierComparison (family V s) unit
    (v V m j) (w V n j) (h V m n hm j)

/-- Second complete comparison, on the same common internal-necklace source. -/
def laterComparison : commonEvaluation V m n hm s j ⟶
    toLaterFiber V m n hm j ⋙ laterEvaluation V n s j :=
  JTActualJointCutSubdivisionEvaluation.laterComparison (family V s) unit
    (v V m j) (w V n j) (h V m n hm j)

section Actual

variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (A : (nerve (TargetComma Q)).Subcomplex)
variable (P : ObjectProperty (JTSemisimplicialSpanEvaluation.Presentation Q A))
variable (a : JTActualSpanPrismLiftCover.Lifted Q A P)

/-- The actual evaluated full-prism object, with its unchanged target `Q`. -/
abbrev actualObject : TargetComma Q :=
  (JTActualSpanPrismLiftCover.evaluation Q A P).obj a

variable (m n : (JTActualSpanMarkedCover.marksDiagram Q A P).obj a)

local instance : Preorder ((JTActualSpanMarkedCover.marksDiagram Q A P).obj a) :=
  inferInstanceAs (Preorder (Marks ((JTActualSpanMarkedCover.native Q A P).obj a).hom))

variable (g : m ⟶ n)

/-- The genuine vertical arrow in the original marked prism-lift fiber. -/
def actualVerticalArrow :
    (⟨a, m⟩ : JTActualSpanMarkedCover.Marked Q A P) ⟶
      (⟨a, n⟩ : JTActualSpanMarkedCover.Marked Q A P) :=
  ⟨𝟙 a, by simpa using g⟩

theorem actualVerticalArrow_base :
    (actualVerticalArrow Q A P a m n g).base = 𝟙 a := rfl

variable (s : JTInternalTraversalLifts.Lift (traversal (actualObject Q A P a)))
variable (j : Joint Q.code)

include g in
/-- The actual vertical arrow determines both cuts over the same joint. -/
theorem actualCut_le :
    earlierCut (actualObject Q A P a) m j ≤
      laterCut (actualObject Q A P a) n j :=
  leOfHom g j

/-- Its first fixed-target comparison includes the common presentation map. -/
def actualEarlierComparison :
    commonEvaluation (actualObject Q A P a) m n (leOfHom g) s j ⟶
      toEarlierFiber (actualObject Q A P a) m n (leOfHom g) j ⋙
        earlierEvaluation (actualObject Q A P a) m s j :=
  earlierComparison (actualObject Q A P a) m n (leOfHom g) s j

/-- Its second comparison uses the same common presentation and original `Q`. -/
def actualLaterComparison :
    commonEvaluation (actualObject Q A P a) m n (leOfHom g) s j ⟶
      toLaterFiber (actualObject Q A P a) m n (leOfHom g) j ⋙
        laterEvaluation (actualObject Q A P a) n s j :=
  laterComparison (actualObject Q A P a) m n (leOfHom g) s j

end Actual

end
end DaggerModels.PartII.JTActualMarkedVerticalCutComparison
