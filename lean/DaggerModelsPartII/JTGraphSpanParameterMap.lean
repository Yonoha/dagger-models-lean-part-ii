import DaggerModelsPartII.JTGraphSpanFamily
import DaggerModelsPartII.JTGraphVariableTimeTransport

/-! Transport the chosen span families in the original variable-source time index. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphSpanParameterMap

open JTGraphSpanFamily
open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphCylinderSpanProjection (nativeCode)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}

private abbrev C := TargetComma Q

open JTGraphCylinderSimplexSpan (SpanIndex smaller)
open JTGraphVariableTimeIndex (Index toNative)
open JTGraphVariableTimeTransport (transport)

private abbrev T := tail (C (Q := Q))
private abbrev S := head (C (Q := Q)) ⋙ nativeCode Q

/-- The collapse, time and exact lift family at an original span. -/
def parameter (P : SpanIndex (C (Q := Q))) : Index (T.obj P) :=
  op ⟨(op (Over.mk ((nativeCode Q).map (traversal.app P))), P.unop.fst.1.unop.unop.fst),
    fun i ↦ ⟨family P i, family_collapse P i⟩⟩

private def nativeOp {P P' : SpanIndex (C (Q := Q))} (f : P ⟶ P') :
    (toNative (T.obj P')).obj ((transport (T.map f)).obj (parameter P)) ⟶
      (toNative (T.obj P')).obj (parameter P') :=
  Over.homMk (S.map f) (by
    change (nativeCode Q).map ((head (C (Q := Q))).map f) ≫
      (nativeCode Q).map (traversal.app P') =
      (nativeCode Q).map (traversal.app P) ≫ (nativeCode Q).map (T.map f)
    rw [← (nativeCode Q).map_comp, ← (nativeCode Q).map_comp]
    exact (nativeCode Q).congr_map (traversal.naturality f))

private def indexArrow {U : C (Q := Q)} {A B : Index U}
    (g : (toNative U).obj A ⟶ (toNative U).obj B)
    (j : (JTGraphVariableTimeIndex.degree U).obj A ⟶
      (JTGraphVariableTimeIndex.degree U).obj B)
    (h : ∀ i, (JTGraphVariableTimeIndex.family U A i).parameter =
        g.left.map ≫
          (JTGraphVariableTimeIndex.family U B (j.toOrderHom i)).parameter) :
    A ⟶ B :=
  (CategoryOfElements.homMk B.unop A.unop (g.op, j.op) (by
    funext i
    apply Subtype.ext
    apply JTGraphLiftTransport.GraphLift.ext
    · change g.left ≫ (JTGraphVariableTimeIndex.family U B (j.toOrderHom i)).collapse =
        (JTGraphVariableTimeIndex.family U A i).collapse
      rw [JTGraphVariableTimeIndex.family_collapse, JTGraphVariableTimeIndex.family_collapse]
      exact Over.w g
    · exact (h i).symm)).op

private abbrev ordinal {P P' : SpanIndex (C (Q := Q))} (f : P ⟶ P') :=
  ((smaller (C (Q := Q))).map f).unop.val.unop

set_option maxHeartbeats 450000 in
/-- Parameter transport is an actual arrow over the two given operators. -/
def parameterMap {P P' : SpanIndex (C (Q := Q))} (f : P ⟶ P') :
    (transport (T.map f)).obj (parameter P) ⟶ parameter P' := by
  refine indexArrow (Q := Q) (U := T.obj P')
    (A := (transport (T.map f)).obj (parameter P)) (B := parameter P')
    (nativeOp f) (ordinal f) ?_
  intro i
  change ((JTGraphSpanFamily.family P i).transport (T.map f).left).parameter =
    ((nativeCode Q).map ((head (C (Q := Q))).map f)).map ≫
      (JTGraphSpanFamily.family P' ((ordinal f).toOrderHom i)).parameter
  have h := JTGraphSpanFamily.family_map (W := W) (x := x) (y := y) (Q := Q)
    (P := P) (P' := P') f i
  exact congrArg (fun D ↦ D.parameter) h

/-- The native operator retains the original larger-simplex prefix. -/
theorem parameterMap_left {P P' : SpanIndex (C (Q := Q))} (f : P ⟶ P') :
    (parameterMap (Q := Q) f).unop.val.1.unop.left = S.map f := rfl

/-- The time operator is the actual smaller-simplex operator. -/
theorem parameterMap_time {P P' : SpanIndex (C (Q := Q))} (f : P ⟶ P') :
    (parameterMap (Q := Q) f).unop.val.2.unop = ordinal f := rfl

/-- Both original cylinder operators are retained by parameter transport. -/
theorem parameterMap_joint {P P' : SpanIndex (C (Q := Q))} (f : P ⟶ P') :
    (JTGraphVariableTimeIndex.joint (T.obj P')).map (parameterMap (Q := Q) f) =
      (JTGraphCylinderSimplexSpan.index (C (Q := Q)) (nativeCode Q)).map f := by
  apply Prod.ext
  · exact parameterMap_left f
  · exact parameterMap_time f

end
end DaggerModels.PartII.JTGraphSpanParameterMap

