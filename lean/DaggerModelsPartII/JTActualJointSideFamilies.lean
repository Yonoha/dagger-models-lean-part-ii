import DaggerModelsPartII.JTActualJointCutPrism
import DaggerModelsPartII.JTComposedPrismLabelSingleton
import DaggerModelsPartII.JTActualJointSideWhiskerNative
import DaggerModelsPartII.JTJointEndpointRelativeLift
import DaggerModelsPartII.JTJointSideWhisker
import DaggerModelsPartII.JTWhiskerEdgeCoefficient
import DaggerModelsPartII.JTJointPaddedOverlapEvaluation

/-! Actual ordered left and right prisms from the full original cut and a relative endpoint lift. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTActualJointSideFamilies

open OrderedNecklaceVertexPoints
open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row vertexPoint)
open JTComposedPrismLabels (Coefficients rawProduct)
open JTActualJointCutPrism (leftCoefficient rightCoefficient leftParameter rightParameter
  vertexRow left_first left_last right_first right_last)
open JTActualJointMarkedEvaluation (left right)
open JTParametrizedBeadGraph (jointCoefficient)
open JTTargetJointMarks (Joint)
open TwoBeadEndpointLabel (edgeLabelFromRow jointLabelFromRow jointLabelFromRow_vertex)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev J := GroupoidSimplex.parameter
private abbrev E := single 1

variable {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {A : Type} [SmallCategory A] {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (a : A) (j : Joint Q.code)
private abbrev T := (codes L).obj a
private abbrev k := (JTJointRelativeGraphFamily.coefficient (L := L)).obj a
private abbrev n := time.obj a
private abbrev I := J.obj (n (time := time) a)
private abbrev z := jointCoefficient (Q := Q) j
variable (v : Fin ((T (L := L) a).len + 1))
variable (hv : orderMap (F.collapse.app a).map v = j.val)

/-- Both the full time map and the old row restricted to its used ordinal face. -/
structure CutSupport where
  degree : SimplexCategory
  inclusion : degree ⟶ k (L := L) a
  mono : Mono inclusion
  timeMap : (Δ[0] : SSet.{0}) ⊗ I (time := time) a ⟶ J.obj degree
  time_eq : (pointAt (T (L := L) a) (ULift.up v) ⊗ₘ 𝟙 (I (time := time) a)) ≫
      F.parameter a = timeMap ≫ J.map inclusion
  row_eq : std.map inclusion ≫ vertexRow (L := L) a v =
    term (std.obj degree) ≫ vertexPoint W (z j)

variable (S : CutSupport F a j v)
variable (hW : letI : ModelCategory Source :=
  InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)

private theorem left_time :
    (pointAt (cutLeft (T (L := L) a) v) (ULift.up (Fin.last _)) ⊗ₘ
      𝟙 (I (time := time) a)) ≫ leftParameter F a v =
      S.timeMap ≫ J.map S.inclusion := by
  unfold leftParameter
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp,
    DaggerOriginalProductGadget.cutLeft_joint]
  exact S.time_eq

private theorem right_time :
    (pointAt (cutRight (T (L := L) a) v) (ULift.up 0) ⊗ₘ
      𝟙 (I (time := time) a)) ≫ rightParameter F a v =
      S.timeMap ≫ J.map S.inclusion := by
  unfold rightParameter
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp,
    DaggerOriginalProductGadget.cutRight_joint]
  exact S.time_eq

include hW in
private theorem left_edge_exists :
    ∃ e : std.obj (k (L := L) a) ⟶ row W ⦋1⦌,
      std.map S.inclusion ≫ e = JTJointEndpointRelativeLift.identityOnFace W (z j) ∧
      e ≫ JTProjectiveOrderedFiberComparison.endpoint W 0 = vertexRow (L := L) a v ∧
      e ≫ JTProjectiveOrderedFiberComparison.endpoint W 1 =
        term (std.obj (k (L := L) a)) ≫ vertexPoint W (z j) := by
  haveI := S.mono
  obtain ⟨e, he, hpair⟩ := JTJointEndpointRelativeLift.exists_edge W S.inclusion
    (vertexRow (L := L) a v) (z j) hW S.row_eq
  exact ⟨e, he, JTJointEndpointRelativeLift.boundaryPair_endpoints W _ _ hpair⟩

include hW in
private theorem right_edge_exists :
    ∃ e : std.obj (k (L := L) a) ⟶ row W ⦋1⦌,
      std.map S.inclusion ≫ e = JTJointEndpointRelativeLift.identityOnFace W (z j) ∧
      e ≫ JTProjectiveOrderedFiberComparison.endpoint W 0 =
        term (std.obj (k (L := L) a)) ≫ vertexPoint W (z j) ∧
      e ≫ JTProjectiveOrderedFiberComparison.endpoint W 1 = vertexRow (L := L) a v := by
  haveI := S.mono
  obtain ⟨e, he, hpair⟩ := JTJointEndpointRelativeLift.exists_reverse_edge W S.inclusion
    (vertexRow (L := L) a v) (z j) hW S.row_eq
  exact ⟨e, he, JTJointEndpointRelativeLift.reverseBoundaryPair_endpoints W _ _ hpair⟩

section EdgeChoice

variable (e : std.obj (k (L := L) a) ⟶ row W ⦋1⦌)

variable (e₀ : e ≫ JTProjectiveOrderedFiberComparison.endpoint W 0 = vertexRow (L := L) a v)
variable (e₁ : e ≫ JTProjectiveOrderedFiberComparison.endpoint W 1 =
  term (std.obj (k (L := L) a)) ≫ vertexPoint W (z j))

/-- The actual left coefficient with a specified relative ending edge. -/
def leftCoefficientsOf :
    Coefficients W (cutLeft (T (L := L) a) v) E (k (L := L) a) x (z j) where
  left := leftCoefficient (L := L) a v
  right := e ≫ edgeLabelFromRow W
  seam := by rw [left_last, JTWhiskerEdgeCoefficient.first, e₀]
  first := left_first (L := L) a v
  last := by rw [JTWhiskerEdgeCoefficient.last, e₁, Category.assoc, jointLabelFromRow_vertex]

/-- The actual right coefficient with a specified relative starting edge. -/
def rightCoefficientsOf
    (h₀ : e ≫ JTProjectiveOrderedFiberComparison.endpoint W 0 =
      term (std.obj (k (L := L) a)) ≫ vertexPoint W (z j))
    (h₁ : e ≫ JTProjectiveOrderedFiberComparison.endpoint W 1 = vertexRow (L := L) a v) :
    Coefficients W E (cutRight (T (L := L) a) v) (k (L := L) a) (z j) y where
  left := e ≫ edgeLabelFromRow W
  right := rightCoefficient (L := L) a v
  seam := by rw [right_first, JTWhiskerEdgeCoefficient.last, h₁]
  first := by rw [JTWhiskerEdgeCoefficient.first, h₀, Category.assoc, jointLabelFromRow_vertex]
  last := right_last (L := L) a v

end EdgeChoice

/-- The actual old left coefficient followed by a correcting edge. -/
def leftCoefficients : Coefficients W (cutLeft (T (L := L) a) v) E (k (L := L) a) x (z j) :=
  leftCoefficientsOf a j v (left_edge_exists F a j v S hW).choose
    (left_edge_exists F a j v S hW).choose_spec.2.1
    (left_edge_exists F a j v S hW).choose_spec.2.2

/-- The actual old right coefficient preceded by a correcting edge. -/
def rightCoefficients : Coefficients W E (cutRight (T (L := L) a) v) (k (L := L) a) (z j) y :=
  rightCoefficientsOf a j v (right_edge_exists F a j v S hW).choose
    (right_edge_exists F a j v S hW).choose_spec.2.1
    (right_edge_exists F a j v S hW).choose_spec.2.2

/-- The ending edge of the left cut is the identity on its used coefficient face. -/
theorem leftEdge_onFace :
    std.map S.inclusion ≫ (leftCoefficients F a j v S hW).right =
      JTConstantOrderedLabel.constantCoefficient W (z j) E S.degree :=
  JTWhiskerEdgeCoefficient.onFace W S.inclusion (z j) _
    (left_edge_exists F a j v S hW).choose_spec.1

/-- The starting edge of the right cut is the identity on its used coefficient face. -/
theorem rightEdge_onFace :
    std.map S.inclusion ≫ (rightCoefficients F a j v S hW).left =
      JTConstantOrderedLabel.constantCoefficient W (z j) E S.degree :=
  JTWhiskerEdgeCoefficient.onFace W S.inclusion (z j) _
    (right_edge_exists F a j v S hW).choose_spec.1

private abbrev f := F.collapse.app a
private abbrev cL := JTActualJointSideWhiskerNative.leftNative Q j (f F a) v hv
private abbrev cR := JTActualJointSideWhiskerNative.rightNative Q j (f F a) v hv

private theorem collapseEdge :
    (JTOrderedLabelJointInsertion.toPoint E).map =
      term E.toSSet := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

set_option maxHeartbeats 1600000 in
/-- A specified relative edge realizes over the actual left target. -/
theorem leftProductOf
    (C : Coefficients W (cutLeft (T (L := L) a) v) E (k (L := L) a) x (z j))
    (hi : C.left = leftCoefficient (L := L) a v)
    (he : std.map S.inclusion ≫ C.right =
      JTConstantOrderedLabel.constantCoefficient W (z j) E S.degree) :
    rawProduct W (JTJointSideWhisker.appendParameter (leftParameter F a v))
      (JTComposedPrismLabels.coefficient C) =
    fst (wedge (cutLeft (T (L := L) a) v) E).toSSet (I (time := time) a) ≫
      (cL F a j v hv).map ≫ (left Q j).map := by
  refine JTJointSideWhisker.append_raw (leftParameter F a v) C
    S.inclusion S.timeMap (left_time F a j v S) ?_ ((cL F a j v hv).map ≫ (left Q j).map)
    ?_ ?_
  · exact he
  · rw [hi, JTActualJointSideWhiskerNative.left_raw_interior]
    exact JTActualJointCutPrism.left_raw F a v
  · change wedgeιRight _ _ ≫ (cL F a j v hv).map ≫ (left Q j).map = _
    rw [JTActualJointSideWhiskerNative.left_raw_whisker, collapseEdge]
    exact congrArg (fun g ↦ term E.toSSet ≫ g)
      (JTJointPaddedOverlapEvaluation.target_map (Q := Q) j).symm

set_option maxHeartbeats 1600000 in
/-- The full corrected left prism has the exact raw map into the original left target. -/
theorem leftProduct :
    rawProduct W (JTJointSideWhisker.appendParameter (leftParameter F a v))
      (JTComposedPrismLabels.coefficient (leftCoefficients F a j v S hW)) =
    fst (wedge (cutLeft (T (L := L) a) v) E).toSSet (I (time := time) a) ≫
      (cL F a j v hv).map ≫ (left Q j).map :=
  leftProductOf F a j v hv S (leftCoefficients F a j v S hW) rfl
    (leftEdge_onFace F a j v S hW)

set_option maxHeartbeats 1600000 in
/-- A specified relative edge realizes over the actual right target. -/
theorem rightProductOf
    (C : Coefficients W E (cutRight (T (L := L) a) v) (k (L := L) a) (z j) y)
    (hi : C.right = rightCoefficient (L := L) a v)
    (he : std.map S.inclusion ≫ C.left =
      JTConstantOrderedLabel.constantCoefficient W (z j) E S.degree) :
    rawProduct W (JTJointSideWhisker.prependParameter (rightParameter F a v))
      (JTComposedPrismLabels.coefficient C) =
    fst (wedge E (cutRight (T (L := L) a) v)).toSSet (I (time := time) a) ≫
      (cR F a j v hv).map ≫ (right Q j).map := by
  refine JTJointSideWhisker.prepend_raw (rightParameter F a v) C
    S.inclusion S.timeMap (right_time F a j v S) ?_ ((cR F a j v hv).map ≫ (right Q j).map)
    ?_ ?_
  · exact he
  · rw [hi, JTActualJointSideWhiskerNative.right_raw_interior]
    exact JTActualJointCutPrism.right_raw F a v
  · change wedgeιLeft _ _ ≫ (cR F a j v hv).map ≫ (right Q j).map = _
    rw [JTActualJointSideWhiskerNative.right_raw_whisker, collapseEdge]
    exact congrArg (fun g ↦ term E.toSSet ≫ g)
      (JTJointPaddedOverlapEvaluation.target_map (Q := Q) j).symm

set_option maxHeartbeats 1600000 in
/-- The full corrected right prism has the exact raw map into the original right target. -/
theorem rightProduct :
    rawProduct W (JTJointSideWhisker.prependParameter (rightParameter F a v))
      (JTComposedPrismLabels.coefficient (rightCoefficients F a j v S hW)) =
    fst (wedge E (cutRight (T (L := L) a) v)).toSSet (I (time := time) a) ≫
      (cR F a j v hv).map ≫ (right Q j).map :=
  rightProductOf F a j v hv S (rightCoefficients F a j v S hW) rfl
    (rightEdge_onFace F a j v S hW)

set_option maxHeartbeats 1300000 in
/-- The original left target with its actual ordered full-prism evaluation at the chosen cut. -/
def leftFamily :=
  JTComposedPrismLabelSingleton.family (left Q j) (leftCoefficients F a j v S hW)
    (cL F a j v hv) (JTJointSideWhisker.appendParameter (leftParameter F a v))
    (leftProduct F a j v hv S hW)

set_option maxHeartbeats 1300000 in
/-- The original right target with its actual ordered full-prism evaluation at the chosen cut. -/
def rightFamily :=
  JTComposedPrismLabelSingleton.family (right Q j) (rightCoefficients F a j v S hW)
    (cR F a j v hv) (JTJointSideWhisker.prependParameter (rightParameter F a v))
    (rightProduct F a j v hv S hW)

end
end DaggerModels.PartII.JTActualJointSideFamilies
