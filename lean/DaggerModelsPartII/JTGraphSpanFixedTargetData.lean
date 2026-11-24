import DaggerModelsPartII.JTGraphSpanParameterMap
import DaggerModelsPartII.JTGraphVariableParametrizedFamilyTransport

/-! The complete graph and raw equation at each original simplex span. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphSpanFixedTargetData

open JTGraphFactoredPresentation (TargetComma)
open JTProjectiveOrderedFiberComparison (row)
open JTGraphCylinderSimplexSpan (SpanIndex index)
open JTGraphSpanFamily (tail)
open JTGraphCylinderSpanProjection (nativeCode)
open JTGraphSpanParameterMap (parameter)
open JTGraphVariableTimeTraversal (labels)
open JTGraphVariableParametrizedFamily (coherentFamily)
open JTGraphLiftTransport (degreeOperator)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTGraphParameterInterpolation (interpolate)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}

private abbrev C := TargetComma Q
private abbrev T := tail (C (Q := Q))
private abbrev nativeTime := index (C (Q := Q)) (nativeCode Q)

variable (P : SpanIndex (C (Q := Q)))

/-- The actual native code and coefficient label of a span keep the original final object. -/
abbrev labelAt := (labels (T.obj P)).obj (parameter (Q := Q) P)

/-- The entire original graph over both the native source and the time simplex. -/
abbrev parameterAt := (coherentFamily (T.obj P)).parameter (parameter (Q := Q) P)

/-- The full native collapse keeps the specified map into the original target. -/
abbrev collapseAt := (coherentFamily (T.obj P)).collapse.app (parameter (Q := Q) P)

/-- The full graph realizes over the exact original fixed target. -/
theorem rawAt :
    (JTParametrizedTargetLiftTransport.graph (i := labelAt P) (parameterAt P)).right ≫
      ((DecoratedCylinderNecklacePresentation.underCocone W x y).app (labelAt P)).right =
    NecklaceCylinderAugmentation.augmentation ((nativeTime (Q := Q)).obj P).1
      ((nativeTime (Q := Q)).obj P).2 ≫ (collapseAt P).map ≫ Q.map :=
  (coherentFamily (T.obj P)).raw (parameter (Q := Q) P)

set_option maxHeartbeats 650000 in
/-- The actual span graph square combines the native prefix, the smaller
simplex's time operator, and the final object's coefficient suffix. -/
theorem parameterAt_square {P P' : SpanIndex (C (Q := Q))} (f : P ⟶ P') :
    (((nativeTime (Q := Q)).map f).1.map ⊗ₘ J.map ((nativeTime (Q := Q)).map f).2) ≫
      parameterAt P' = parameterAt P ≫ J.map (degreeOperator (T.map f).left) := by
  let g := ((nativeTime (Q := Q)).map f).1
  let j := ((nativeTime (Q := Q)).map f).2
  let r := degreeOperator (T.map f).left
  let n := ((nativeTime (Q := Q)).obj P).2
  let V := ((nativeTime (Q := Q)).obj P').1
  let a := fun i ↦ (JTGraphSpanFamily.family (W := W) (x := x) (y := y) (Q := Q) P i).parameter
  let b := fun i ↦ (JTGraphSpanFamily.family (W := W) (x := x) (y := y) (Q := Q) P' i).parameter
  have h : (fun i ↦ g.map ≫ b (j.toOrderHom i)) = fun i ↦ a i ≫ J.map r := by
    funext i
    let D := JTGraphLiftTransport.GraphLift (T.obj P').left ((nativeTime (Q := Q)).obj P).1
    have hh := JTGraphSpanFamily.family_map (W := W) (x := x) (y := y) (Q := Q)
      (P := P) (P' := P') f i
    have he := congrArg (fun z : D ↦ z.parameter) hh
    exact he.symm
  change (g.map ⊗ₘ J.map j) ≫ interpolate b = interpolate a ≫ J.map r
  calc
    _ = (g.map ⊗ₘ 𝟙 (J.obj n)) ≫ (𝟙 V.toSSet ⊗ₘ J.map j) ≫ interpolate b := by
      rw [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    _ = _ := by
      rw [JTInterpolatedCylinderReindex.interpolate_reindex,
        JTInterpolatedCylinderSource.interpolate_source, h,
        JTInterpolatedCylinderOutput.interpolate_output]

end

end DaggerModels.PartII.JTGraphSpanFixedTargetData
