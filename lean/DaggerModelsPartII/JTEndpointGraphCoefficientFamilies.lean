import DaggerModelsPartII.JTEndpointGraphCoefficientChoices
import DaggerModelsPartII.JTCommonCoefficientBeadLift
import DaggerModelsPartII.JTNormalizedGraphTargetArrow

/-! The actual ordered row families on the common-coefficient slice. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTEndpointGraphCoefficientFamilies

open OrdinaryJTRealization (realization)
open JTReversalInput JTProjectiveOrderedFiberComparison JTMixedGraphEndpointLifts
open JTEndpointSimplexSlice JTEndpointRowGraphOperators JTEndpointGraphCoefficientSlice
open JTEndpointGraphCoefficientChoices JTEndpointNormalizationLifts
open JTEndpointRowGraphNormalization (vertexAt)
open JTHigherCommonMixedGraphFamilies JTCommonCoefficientLiftChoices
open JTMixedGraphRawRefinement JTMixedGraphVerticalArrow
open JTHigherInterleavedParameter (common)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev std := SSet.stdSimplex.{0}
private abbrev Δ (m : SimplexCategory) := std.obj m
private abbrev J := GroupoidSimplex.parameter
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {d : ℕ} {q : Δ ⦋d⦌ ⟶ realization.obj (ordinaryInput.obj W)}
variable (P : MixedGraphs q)
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (hx : SSet.yonedaEquiv (vertex ⦋d⦌ 0 ≫ q) = rawVertex W x)
variable (hy : SSet.yonedaEquiv (vertex ⦋d⦌ (Fin.last d) ≫ q) = rawVertex W y)

theorem leftBase_eq (A : Over P) :
    leftBase P x = prod.lift (term (Δ (coefficientDegree.obj P)) ≫ vertexPoint W x)
      (parentRow P A ≫ rowVertex W (horizontalDegree A.left.unop) 0) := by
  have h := parentRow_vertex P A 0
  rw [A.hom.unop.base.unop.left.2.1] at h
  rw [h]

theorem rightBase_eq (A : Over P) :
    rightBase P y = prod.lift
      (parentRow P A ≫ rowVertex W (horizontalDegree A.left.unop)
        (Fin.last (horizontalDegree A.left.unop).len))
      (term (Δ (coefficientDegree.obj P)) ≫ vertexPoint W y) := by
  have h := parentRow_vertex P A (Fin.last (horizontalDegree A.left.unop).len)
  have ht : A.hom.unop.base.unop.left.1.toOrderHom (Fin.last (horizontalDegree A.left.unop).len) =
      Fin.last (horizontalDegree P.unop).len := A.hom.unop.base.unop.left.2.2
  rw [ht] at h
  rw [h]

variable (U : Index P hx hy)

abbrev child : Over P := (base P hx hy).obj U
abbrev dim : ℕ := (horizontalDegree (child P hx hy U).left.unop).len
abbrev nativeCode := (codes P).obj (child P hx hy U)
abbrev param := (graph (child P hx hy U).left.unop).obj.parameter
abbrev coeff := ((coefficients P).obj (child P hx hy U)).hom
abbrev timeDegree := SemiSimplexCategory.toSimplexCategory.obj ((semiTime P hx hy).obj U)

private abbrev leftSq :
    CommSq (vertexPoint W x ≫ identityFamily W)
      (vertexAt (child P hx hy U).left.unop 0)
      (endpointArrow W)
      (std.map (coeff P hx hy U) ≫
        prod.lift (term (Δ (coefficientDegree.obj P)) ≫ vertexPoint W x)
          (parentRow P (child P hx hy U) ≫ rowVertex W ⦋dim P hx hy U⦌ 0)) := by
  have h : leftBase P x = prod.lift (term (Δ (coefficientDegree.obj P)) ≫ vertexPoint W x)
      (parentRow P (child P hx hy U) ≫ rowVertex W ⦋dim P hx hy U⦌ 0) :=
    leftBase_eq P (child P hx hy U)
  rw [← h]
  exact leftSquare P hx (child P hx hy U)

private abbrev rightSq :
    CommSq (vertexPoint W y ≫ identityFamily W)
      (vertexAt (child P hx hy U).left.unop (Fin.last (dim P hx hy U)))
      (endpointArrow W)
      (std.map (coeff P hx hy U) ≫
        prod.lift (parentRow P (child P hx hy U) ≫
          rowVertex W ⦋dim P hx hy U⦌ (Fin.last (dim P hx hy U)))
          (term (Δ (coefficientDegree.obj P)) ≫ vertexPoint W y)) := by
  have h : rightBase P y = prod.lift (parentRow P (child P hx hy U) ≫
      rowVertex W ⦋dim P hx hy U⦌ (Fin.last (dim P hx hy U)))
      (term (Δ (coefficientDegree.obj P)) ≫ vertexPoint W y) :=
    rightBase_eq P (child P hx hy U)
  rw [← h]
  exact rightSquare P hy (child P hx hy U)

private def leftFamily : Extension (leftSq P hx hy U) (timeDegree P hx hy U) where
  map := (leftChoice P hx hy U).map
  stationary := (leftChoice P hx hy U).stationary
  over := (leftChoice P hx hy U).over.trans
    (congrArg (std.map (JTCommonCoefficientParameter.base (coeff P hx hy U)
      (timeDegree P hx hy U)) ≫ ·) (leftBase_eq P (x := x) (child P hx hy U)))

private def rightFamily : Extension (rightSq P hx hy U) (timeDegree P hx hy U) where
  map := (rightChoice P hx hy U).map
  stationary := (rightChoice P hx hy U).stationary
  over := (rightChoice P hx hy U).over.trans
    (congrArg (std.map (JTCommonCoefficientParameter.base (coeff P hx hy U)
      (timeDegree P hx hy U)) ≫ ·) (rightBase_eq P (y := y) (child P hx hy U)))

/-- The middle label is the restricted parent row, and the outer labels are the chosen lifts. -/
abbrev families :=
  commonChoiceFamilies (d := dim P hx hy U) (coeff P hx hy U) (timeDegree P hx hy U)
    (parentRow P (child P hx hy U)) (param P hx hy U) x y
    (leftFamily P hx hy U) (rightFamily P hx hy U) 0

/-- The original horizontal operator into the fixed raw simplex. -/
abbrev toFixedBead : single (dim P hx hy U) ⟶ single d :=
  bead.map ((horizontal.obj (child P hx hy U).left).hom)

/-- The realization of the enlarged middle label equals the original fixed-target restriction. -/
theorem raw_eq :
    nativeRawGraph W (dim P hx hy U) (coefficientDegree.obj P)
      (parentRow P (child P hx hy U)) (param P hx hy U ≫ J.map (coeff P hx hy U)) =
    (toFixedBead P hx hy U).map ≫ (JTNormalizedGraphTargetArrow.target hx hy).map := by
  let A := (child P hx hy U).left.unop
  have hF := coefficient_factor P (child P hx hy U)
  rw [← nativeRawGraph_reindex, hF]
  have h := JTRowGraphNormalizationDiagram.raw_eq (d := dim P hx hy U) (graph A)
  change (singleIso (dim P hx hy U)).hom ≫
    rawGraph W ⦋dim P hx hy U⦌ (graph A).obj.degree (graphCoefficient A) (graph A).obj.parameter = _
  rw [h]
  change (singleIso (dim P hx hy U)).hom ≫ (std.map A.base.unop.hom.1 ≫ q) =
    ((singleIso (dim P hx hy U)).hom ≫ std.map A.base.unop.hom.1 ≫ (singleIso d).inv) ≫
      ((singleIso d).hom ≫ q)
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end
end DaggerModels.PartII.JTEndpointGraphCoefficientFamilies
