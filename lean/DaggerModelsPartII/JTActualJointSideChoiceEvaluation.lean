import DaggerModelsPartII.JTActualJointSideChoiceTransport
import DaggerModelsPartII.JTActualJointSideParameterTransport
import DaggerModelsPartII.JTActualSourceJointSideEvaluation

/-! Exact comparisons of fully corrected cuts under a strict marked arrow and choice restriction. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTActualJointSideChoiceEvaluation

open JTParametrizedTargetFamilies (Family codes)
open JTParametrizedTargetLiftTransport (graph)
open JTTargetJointMarks (Joint)
open JTActualJointSideChoiceTransport (Choices restrictChoices leftLabelMap rightLabelMap)
open JTActualJointSideFamilies (leftProductOf rightProductOf)
open JTActualJointSideWhiskerNative (leftNative rightNative)
open JTActualJointMarkedEvaluation (left right)
open JTActualJointCutPrism (leftParameter rightParameter)
open JTJointSideWhisker (appendParameter prependParameter)
open JTComposedPrismLabels (index orderedPoint orderedPoint_coefficient reduced_raw)
open NecklaceCylinderAugmentation (augmentation)
open DecoratedCylinderNecklacePresentation (underCocone)
open JTParametrizedBeadGraph (jointCoefficient)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {A : Type} [SmallCategory A]
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code)
private abbrev z := jointCoefficient (Q := Q) j
private abbrev E := single 1
private abbrev T (a : A) := (codes L).obj a
private abbrev pL (a : A) (v : Fin ((T (L := L) a).len + 1)) :=
  appendParameter (leftParameter F a v)
private abbrev pR (a : A) (v : Fin ((T (L := L) a).len + 1)) :=
  prependParameter (rightParameter F a v)
private abbrev cL (a : A) (v : Fin ((T (L := L) a).len + 1))
    (hv : orderMap (F.collapse.app a).map v = j.val) :=
  leftNative Q j (F.collapse.app a) v hv
private abbrev cR (a : A) (v : Fin ((T (L := L) a).len + 1))
    (hv : orderMap (F.collapse.app a).map v = j.val) :=
  rightNative Q j (F.collapse.app a) v hv

variable {a : A} {v : Fin ((T (L := L) a).len + 1)}
variable {hv : orderMap (F.collapse.app a).map v = j.val}
variable (C : Choices F j a v hv)

set_option maxHeartbeats 150000 in
/-- The actual left time family uses the specified relative ending edge. -/
def leftFamily := by
  let d := Choices.leftCoefficients F j C
  let S := JTActualSourceJointSideEvaluation.support F a j v hv
  have he := JTWhiskerEdgeCoefficient.onFace W S.inclusion (z j) C.ending C.ending_face
  have hprod := leftProductOf F a j v hv S d rfl he
  exact JTComposedPrismLabelSingleton.family (left Q j) d (cL F j a v hv)
    (pL F a v) hprod

set_option maxHeartbeats 150000 in
/-- The actual right time family uses the specified relative starting edge. -/
def rightFamily := by
  let d := Choices.rightCoefficients F j C
  let S := JTActualSourceJointSideEvaluation.support F a j v hv
  have he := JTWhiskerEdgeCoefficient.onFace W S.inclusion (z j) C.starting C.starting_face
  have hprod := rightProductOf F a j v hv S d rfl he
  exact JTComposedPrismLabelSingleton.family (right Q j) d (cR F j a v hv)
    (pR F a v) hprod

/-- Evaluate all internal necklaces of the actual left time family. -/
def leftEvaluation := JTParametrizedTargetFamilies.evaluate (leftFamily F j C)

/-- Evaluate all internal necklaces of the actual right time family. -/
def rightEvaluation := JTParametrizedTargetFamilies.evaluate (rightFamily F j C)

private theorem leftNative_eq {U : NecklaceCode} (u : Fin (U.len + 1))
    {g g' : U ⟶ Q.code} (h : g = g')
    (hg : orderMap g.map u = j.val) (hg' : orderMap g'.map u = j.val) :
    leftNative Q j g u hg = leftNative Q j g' u hg' := by
  subst g'
  rfl

private theorem rightNative_eq {U : NecklaceCode} (u : Fin (U.len + 1))
    {g g' : U ⟶ Q.code} (h : g = g')
    (hg : orderMap g.map u = j.val) (hg' : orderMap g'.map u = j.val) :
    rightNative Q j g u hg = rightNative Q j g' u hg' := by
  subst g'
  rfl

variable {b : A} (f : a ⟶ b) {w : Fin ((T (L := L) b).len + 1)}
variable {hw : orderMap (F.collapse.app b).map w = j.val}
variable (h : orderMap ((codes L).map f).map v = w)
variable (D : Choices F j b w hw)

private theorem original_collapse :
    ((codes L).map f) ≫ F.collapse.app b = F.collapse.app a :=
  (F.collapse.naturality f).trans (Category.comp_id _)

set_option maxHeartbeats 150000 in
/-- The exact left comparison with every original arrow, when the cut is preserved. -/
def leftComparison :=
  JTParametrizedTargetLiftTransport.compare (left Q j) (leftLabelMap F j f (hv := hv) h D)
    (time.map f) (pL F a v) (pL F b w) (cL F j a v hv) (cL F j b w hw)
    ((JTActualJointSideNativeTransport.leftNative_comp Q j ((codes L).map f) (F.collapse.app b)
      v w h hw).trans (leftNative_eq j v (original_collapse F f) _ hv))
    (JTActualJointSideParameterTransport.left_map F f v w h)
    ((leftFamily F j (restrictChoices F j f (hv := hv) h D)).raw (Discrete.mk PUnit.unit))
    ((leftFamily F j D).raw (Discrete.mk PUnit.unit))

set_option maxHeartbeats 150000 in
/-- The exact right comparison with every original arrow, when the cut is preserved. -/
def rightComparison :=
  JTParametrizedTargetLiftTransport.compare (right Q j) (rightLabelMap F j f (hv := hv) h D)
    (time.map f) (pR F a v) (pR F b w) (cR F j a v hv) (cR F j b w hw)
    ((JTActualJointSideNativeTransport.rightNative_comp Q j ((codes L).map f) (F.collapse.app b)
      v w h hw).trans (rightNative_eq j v (original_collapse F f) _ hv))
    (JTActualJointSideParameterTransport.right_map F f v w h)
    ((rightFamily F j (restrictChoices F j f (hv := hv) h D)).raw (Discrete.mk PUnit.unit))
    ((rightFamily F j D).raw (Discrete.mk PUnit.unit))

end
end DaggerModels.PartII.JTActualJointSideChoiceEvaluation
