import DaggerModelsPartII.JTEndpointGraphOverlapEvaluation
import DaggerModelsPartII.JTEndpointGraphOverlapRestriction

/-! The old decorated labels embed naturally into the entire overlap label. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace
open scoped Prod

namespace DaggerModels.PartII.JTEndpointGraphOverlapLabels

open OrdinaryJTRealization (realization)
open JTReversalInput (ordinaryInput)
open JTProjectiveOrderedFiberComparison (row)
open JTMixedGraphEndpointLifts (vertex)
open JTEndpointRowGraphOperators (horizontalDegree graphCoefficient)
open JTEndpointGraphCoefficientSlice (MixedGraphs coefficientDegree parentRow coefficient_factor)
open JTEndpointGraphCoefficientOverlap
open JTEndpointGraphOverlapChoices
open JTEndpointGraphOverlapFamilies
open JTEndpointGraphOverlapRestriction
open OrderedNecklaceVertexPoints (boundaryPoint)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev std := SSet.stdSimplex.{0}
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev rows (W : Source) := JTRealizationDiagonal.ordinaryCurry.obj (ordinaryInput.obj W)

variable {W : Source} {d m : ℕ} {q : (Δ[d] : SSet.{0}) ⟶ realization.obj (ordinaryInput.obj W)}
variable (P : MixedGraphs q) (parents : Fin (m + 1) → MixedGraphs q)
variable (refineTo : ∀ e, parents e ⟶ P)
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (hx : SSet.yonedaEquiv (vertex ⦋d⦌ 0 ≫ q) = rawVertex W x)
variable (hy : SSet.yonedaEquiv (vertex ⦋d⦌ (Fin.last d) ≫ q) = rawVertex W y)

private abbrev I := Index P parents refineTo hx hy
private abbrev F := projection P parents refineTo hx hy
private abbrev sideLabels (e : Fin (m + 1)) :=
  toSide P parents refineTo hx hy e ⋙ JTEndpointGraphCoefficientLabels.labelIndex (parents e) hx hy
private abbrev bridgeLabels := JTEndpointGraphOverlapEvaluation.labelIndex P parents refineTo hx hy

private theorem parentRow_side (A : Overlap P parents refineTo) (e : Fin (m + 1)) :
    std.map (coefficientDegree.map (refineTo e)) ≫ parentRow P ((toCommon P parents refineTo).obj A) =
      parentRow (parents e) ((toParent P parents refineTo e).obj A) := by
  let a := (refineTo e).unop.base.unop.left.1
  let b := (A.π.app (some e)).unop.base.unop.left.1
  let c := (A.π.app none).unop.base.unop.left.1
  have h := congrArg (fun f : A.pt ⟶ P ↦ f.unop.base.unop.left.1)
    (A.w (WidePullbackShape.Hom.term e))
  change b ≫ a = c at h
  let k := std.map (coefficientDegree.map (refineTo e))
  have hrow : k ≫ parentRow P (Over.mk (refineTo e)) = graphCoefficient (parents e).unop :=
    coefficient_factor P (Over.mk (refineTo e))
  change k ≫ (graphCoefficient P.unop ≫ (rows W).map a.op) = _ at hrow
  change k ≫ graphCoefficient P.unop ≫ (rows W).map c.op =
    graphCoefficient (parents e).unop ≫ (rows W).map b.op
  rw [← h, op_comp, (rows W).map_comp, ← Category.assoc (graphCoefficient P.unop),
    ← Category.assoc k, hrow]

private abbrev sideOp (e : Fin (m + 1)) (U : I P parents refineTo hx hy) :=
  (sideToBridge P parents refineTo e).app ((F P parents refineTo hx hy).obj U)

private theorem sideMiddle (e : Fin (m + 1)) (U : I P parents refineTo hx hy) :
    let V := (toSide P parents refineTo hx hy e).obj U
    std.map (JTCommonCoefficientParameter.base
      (JTEndpointGraphCoefficientFamilies.coeff (parents e) hx hy V)
      (JTEndpointGraphCoefficientFamilies.timeDegree (parents e) hx hy V)) ≫
      parentRow (parents e) (JTEndpointGraphCoefficientFamilies.child (parents e) hx hy V) =
    std.map (sideOp P parents refineTo hx hy e U) ≫
      (std.map (JTFiniteCoefficientBridgeOrder.base (c P parents refineTo hx hy U)
        (u P parents refineTo hx hy U) (n P parents refineTo hx hy U)) ≫
        rowAt P parents refineTo hx hy U) := by
  let A := overlapAt P parents refineTo hx hy U
  let b := JTCommonCoefficientParameter.base (side A e) (n P parents refineTo hx hy U)
  let B := JTFiniteCoefficientBridgeOrder.base (c P parents refineTo hx hy U)
    (u P parents refineTo hx hy U) (n P parents refineTo hx hy U)
  let s := sideOp P parents refineTo hx hy e U
  let h := coefficientDegree.map (refineTo e)
  have hs : s ≫ B = b ≫ h :=
    JTFiniteCoefficientBridgeOrder.side_base (side A) (final A)
      (fun t ↦ coefficientDegree.map (refineTo t)) (side_final A) (n P parents refineTo hx hy U) e
  change std.map b ≫ parentRow (parents e) ((toParent P parents refineTo e).obj A) =
    std.map s ≫ std.map B ≫ parentRow P ((toCommon P parents refineTo).obj A)
  rw [← Category.assoc (std.map s), ← std.map_comp, hs, std.map_comp, Category.assoc,
    parentRow_side P parents refineTo A e]

private theorem sidePoint (e : Fin (m + 1)) (U : I P parents refineTo hx hy) :
    let V := (toSide P parents refineTo hx hy e).obj U
    let a := sideOp P parents refineTo hx hy e U
    let S := TripleBeadEndpointLabel.code (dim P parents refineTo hx hy U)
    (OrderedLabelElements.labelPresheaf W (boundaryPoint W x y)).map
      ((𝟙 S) ×ₘ a).op (JTMixedGraphOrderedLabel.orderedPoint (families P parents refineTo hx hy U)) =
    JTMixedGraphOrderedLabel.orderedPoint (JTEndpointGraphCoefficientFamilies.families (parents e) hx hy V) := by
  dsimp only
  let U' := (toSide P parents refineTo hx hy e).obj U
  let E := families P parents refineTo hx hy U
  let E' := JTEndpointGraphCoefficientFamilies.families (parents e) hx hy U'
  let a := sideOp P parents refineTo hx hy e U
  let S := TripleBeadEndpointLabel.code (dim P parents refineTo hx hy U)
  let G := OrderedNecklaceLabelDiagram.orderedNecklaceLabels W (boundaryPoint W x y)
  change (G.obj (op S)).map a.op
      ((G.map (𝟙 (op S))).app (op _) (JTMixedGraphOrderedLabel.orderedPoint E)) =
    JTMixedGraphOrderedLabel.orderedPoint E'
  rw [G.map_id]
  change (G.obj (op S)).map a.op (JTMixedGraphOrderedLabel.orderedPoint E) =
    JTMixedGraphOrderedLabel.orderedPoint E'
  symm
  apply JTMixedGraphEdgeFamilyReindex.orderedPoint_reindex_of_rows a
    (JTMixedGraphOrderedLabel.families E) (JTMixedGraphOrderedLabel.families E')
  · change E'.left ≫ _ = std.map a ≫ E.left ≫ _
    have he : E'.left = std.map a ≫ E.left := toSide_left P parents refineTo hx hy e U
    rw [he, Category.assoc]
  · change _ ≫ JTNativeRowLabel.labelFromRow W _ = std.map a ≫ _ ≫ JTNativeRowLabel.labelFromRow W _
    rw [← Category.assoc (std.map a), ← sideMiddle P parents refineTo hx hy e U]
  · change E'.right ≫ _ = std.map a ≫ E.right ≫ _
    have he : E'.right = std.map a ≫ E.right := toSide_right P parents refineTo hx hy e U
    rw [he, Category.assoc]

private def labelSideApp (e : Fin (m + 1)) (U : I P parents refineTo hx hy) :
    (sideLabels P parents refineTo hx hy e).obj U ⟶ (bridgeLabels P parents refineTo hx hy).obj U :=
  Quiver.Hom.op ⟨((𝟙 _) ×ₘ sideOp P parents refineTo hx hy e U).op,
    sidePoint P parents refineTo hx hy e U⟩

/-- The whole ordered label of every old chart has its prescribed arrow to the joined label. -/
def toBridgeLabel (e : Fin (m + 1)) :
    sideLabels P parents refineTo hx hy e ⟶ bridgeLabels P parents refineTo hx hy where
  app := labelSideApp P parents refineTo hx hy e
  naturality {U V} f := by
    let r := (F P parents refineTo hx hy).map f
    let v := (JTEndpointGraphOverlapCylinder.nativeCodes P parents refineTo).map r
    let j := (sideParameter P parents refineTo e).map r
    let k := (bridgeParameter P parents refineTo).map r
    let pr := OrderedLabelElements.projection W (boundaryPoint W x y)
    let s := (sideLabels P parents refineTo hx hy e).map f
    let t := (bridgeLabels P parents refineTo hx hy).map f
    let a := labelSideApp P parents refineTo hx hy e U
    let b := labelSideApp P parents refineTo hx hy e V
    have h : pr.map (s ≫ b) = pr.map (a ≫ t) := by
      rw [pr.map_comp, pr.map_comp]
      have hs : pr.map s = (v, j) := rfl
      have ht : pr.map t = (v, k) := rfl
      rw [hs, ht]
      exact Prod.ext ((Category.comp_id v).trans (Category.id_comp v).symm)
        ((sideToBridge P parents refineTo e).naturality r)
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    exact congrArg Quiver.Hom.op h

/-- The label comparison is the original parameter map with the same native code. -/
theorem underDiagram_toBridgeLabel (e : Fin (m + 1)) (U : I P parents refineTo hx hy) :
    (DecoratedCylinderNecklacePresentation.underDiagram W x y).map
      ((toBridgeLabel P parents refineTo hx hy e).app U) =
    (JTNecklaceEndpointCylinder.under
      ((JTEndpointGraphOverlapCylinder.nativeCodes P parents refineTo).obj
        ((F P parents refineTo hx hy).obj U))).map (sideOp P parents refineTo hx hy e U) := by
  apply Under.UnderMorphism.ext
  change JTNecklaceEndpointCylinder.nativeMap (𝟙 _) _ ≫ _ = _
  rw [JTNecklaceEndpointCylinder.nativeMap_id, Category.id_comp]
  rfl

end
end DaggerModels.PartII.JTEndpointGraphOverlapLabels
