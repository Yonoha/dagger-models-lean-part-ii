import DaggerModelsPartII.JTJoinedGraphParameterTransport
import DaggerModelsPartII.JTGraphVariableLabelTransport

/-! Changes of joined labels along the original side arrows at their ordered seam. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTJoinedGraphLabelTransport

open JTGraphFactoredPresentation (TargetComma)
open JTProjectiveOrderedFiberComparison (row)
open JTGraphVariableTimeIndex (timeDiagram toNative)
open JTGraphVariableTimeTraversal (labels)
open JTGraphVariableLabelTransport (labelTransport labelTransport_projection)
open JTGraphLiftTransport (degree degreeOperator projection)
open JTIndependentTargetResolutions (Resolution)
open JTJoinedGraphParameterTransport (transportPair)
open JTParametrizedTargetFamilyJoin (compareLabels compareLabels_map)
open SynchronizedSimplicialParameters (left right)
open JTBinaryPrismParameter (sideMap)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev Native (W : Source) (x y : Vertex W) :=
  NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)

variable {W : Source} {x z y : Vertex W}
variable {P : Native W x z} {Q : Native W z y}
variable {U U' : TargetComma P} {V V' : TargetComma Q}

private abbrev pairLeft (U : TargetComma P) (V : TargetComma Q) :=
  left (timeDiagram U) (timeDiagram V)
private abbrev pairRight (U : TargetComma P) (V : TargetComma Q) :=
  right (timeDiagram U) (timeDiagram V)

private abbrev joined (U : TargetComma P) (V : TargetComma Q) :=
  (Resolution.ofGraph U).join (Resolution.ofGraph V)

variable (a : U ⟶ U') (b : V ⟶ V')

/-- The ordered seam of a pair of original comma arrows is preserved when
the left coefficient retains its last vertex and the right its first. -/
def PreservesSeam : Prop :=
  (degreeOperator a.left).toOrderHom (Fin.last (degree U.left).len) =
    Fin.last (degree U'.left).len ∧
  (degreeOperator b.left).toOrderHom 0 = 0

private def leftComparison :
    pairLeft U V ⋙ labels U ⟶ transportPair a b ⋙ pairLeft U' V' ⋙ labels U' :=
  Functor.whiskerLeft (pairLeft U V) (labelTransport a)

private def rightComparison :
    pairRight U V ⋙ labels V ⟶ transportPair a b ⋙ pairRight U' V' ⋙ labels V' :=
  Functor.whiskerLeft (pairRight U V) (labelTransport b)

private abbrev leftCode (p : SynchronizedSimplicialParameters.Index (timeDiagram U)
    (timeDiagram V)) := ((toNative U).obj ((pairLeft U V).obj p)).left
private abbrev rightCode (p : SynchronizedSimplicialParameters.Index (timeDiagram U)
    (timeDiagram V)) := ((toNative V).obj ((pairRight U V).obj p)).left

variable (h : PreservesSeam a b)

set_option maxHeartbeats 450000 in
/-- Join the two actual original label changes over the common time. -/
def comparison :
    (joined U V).family.labels ⟶ transportPair a b ⋙ (joined U' V').family.labels := by
  let L := (Resolution.ofGraph U).family.precomp (pairLeft U V)
  let R := (Resolution.ofGraph V).family.precomp (pairRight U V)
  let L' := (Resolution.ofGraph U').family.precomp (transportPair a b ⋙ pairLeft U' V')
  let R' := (Resolution.ofGraph V').family.precomp (transportPair a b ⋙ pairRight U' V')
  let α : L.labels ⟶ L'.labels := leftComparison a b
  let β : R.labels ⟶ R'.labels := rightComparison a b
  refine compareLabels (hL := L.last) (hR := R.first) (hL' := L'.last) (hR' := R'.first)
    α β ?_ ?_
  · intro p
    change ((projection (W := W) (x := x) (y := z)).map
      ((labelTransport a).app ((pairLeft U V).obj p))).2.toOrderHom
        (Fin.last (degree U.left).len) = Fin.last (degree U'.left).len
    rw [labelTransport_projection]
    exact h.1
  · intro p
    change ((projection (W := W) (x := z) (y := y)).map
      ((labelTransport b).app ((pairRight U V).obj p))).2.toOrderHom 0 = 0
    rw [labelTransport_projection]
    exact h.2

set_option maxHeartbeats 450000 in
/-- The joined label change is the native identity and the original block map. -/
theorem comparison_projection (p : SynchronizedSimplicialParameters.Index (timeDiagram U)
    (timeDiagram V)) :
    (projection (W := W) (x := x) (y := y)).map ((comparison a b h).app p) =
      (sideMap (𝟙 (leftCode p)) (𝟙 (rightCode p)),
        JTParameterBlockOperators.map (degreeOperator a.left) (degreeOperator b.left)) := by
  unfold comparison
  rw [compareLabels_map]
  · let l := (projection (W := W) (x := x) (y := z)).map
      ((labelTransport a).app ((pairLeft U V).obj p))
    let r := (projection (W := W) (x := z) (y := y)).map
      ((labelTransport b).app ((pairRight U V).obj p))
    change (sideMap l.1 r.1, JTParameterBlockOperators.map l.2 r.2) = _
    dsimp only [l, r]
    rw [labelTransport_projection, labelTransport_projection]
  · exact ((Resolution.ofGraph U).family.precomp (pairLeft U V)).last
  · exact ((Resolution.ofGraph V).family.precomp (pairRight U V)).first
  · exact ((Resolution.ofGraph U').family.precomp (transportPair a b ⋙ pairLeft U' V')).last
  · exact ((Resolution.ofGraph V').family.precomp (transportPair a b ⋙ pairRight U' V')).first

end

end DaggerModels.PartII.JTJoinedGraphLabelTransport
