import DaggerModelsPartII.OrderedNecklaceVertexPoints
import DaggerModelsPartII.OrderedSimplexEndpointFiber
import DaggerModelsPartII.DiagramMappingPushout
import DaggerModelsPartII.ReversalDiscreteFreeColimits
import ChosenNecklaceWedgePushout

/-!
# A whole-parameter label on the actual two-bead necklace

The source is the unchanged native wedge of two single edges. Two full
degree-one edge labels glue when their entire Δ[1]-parameter families agree
at the common vertex. The ordered endpoint boundary equation is retained
by checking the two outer-endpoint equations on the entire parameter.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.TwoBeadEndpointLabel

open ReversalDiscreteFreeColimits OrderedNecklaceLabelDiagram

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev F := discreteFree.{0}
private abbrev E : SSet.{0} := (single 1).toSSet
private abbrev T : DaggerChosenRigidificationNecklace.NecklaceCode :=
  wedge (single 1) (single 1)
private abbrev K : SSet.{0} := Δ[1]

variable (W : Source)

abbrev edgeLabels := diagramMappingSpace (F.obj E) W
abbrev jointLabels := diagramMappingSpace (F.obj (Δ[0] : SSet.{0})) W
abbrev twoBeadLabels := diagramMappingSpace (F.obj T.toSSet) W

/-- Transport an original row-one family to the actual native single-edge
mapping space. The native single edge is sent to the standard simplex by
its retained isomorphism, so the outer endpoint order is unchanged. -/
def edgeLabelFromRow :
    JTProjectiveOrderedFiberComparison.row W ⦋1⦌ ⟶ edgeLabels W :=
  (OrderedSimplexEndpointFiber.freeSimplexRowIso W 1).inv ≫
    diagramMappingPrecomp (F.map (singleIso 1).hom) W

def jointLabelFromRow :
    JTProjectiveOrderedFiberComparison.row W ⦋0⦌ ⟶ jointLabels W :=
  (OrderedSimplexEndpointFiber.freeSimplexRowIso W 0).inv

private theorem nativeEndpoint_coface (i : Fin 2) :
    F.map (pointAt (single 1) (ULift.up i)) ≫ F.map (singleIso 1).hom =
      SegalRepresentables.freeSimplices.map
        (JTXiEndpointCollapseBoundary.ordinaryEndpoint i) := by
  fin_cases i
  · simpa only [OrderedNecklaceLabelDiagram.boundarySimplex,
      OrderedNecklaceLabelDiagram.boundaryNecklace,
      coprod.inl_desc_assoc, singleIso_hom] using
      (OrderedSimplexEndpointFiber.singleBoundary_first)
  · simpa only [OrderedNecklaceLabelDiagram.boundarySimplex,
      OrderedNecklaceLabelDiagram.boundaryNecklace,
      coprod.inr_desc_assoc, singleIso_hom] using
      (OrderedSimplexEndpointFiber.singleBoundary_last)

/-- The public row bridge respects BOTH original outer cofaces. -/
theorem edgeLabelFromRow_endpoint (i : Fin 2) :
    edgeLabelFromRow W ≫ diagramMappingPrecomp
        (F.map (pointAt (single 1) (ULift.up i))) W =
      JTProjectiveOrderedFiberComparison.endpoint W i ≫
        jointLabelFromRow W := by
  have h := OrderedSimplexEndpointFiber.freeSimplexRowIso_endpoint W i
  have h' : diagramMappingPrecomp
      (SegalRepresentables.freeSimplices.map
        (JTXiEndpointCollapseBoundary.ordinaryEndpoint i)) W =
      (OrderedSimplexEndpointFiber.freeSimplexRowIso W 1).hom ≫
        JTProjectiveOrderedFiberComparison.endpoint W i ≫
          (OrderedSimplexEndpointFiber.freeSimplexRowIso W 0).inv := by
    calc
      _ = (diagramMappingPrecomp
            (SegalRepresentables.freeSimplices.map
              (JTXiEndpointCollapseBoundary.ordinaryEndpoint i)) W ≫
              (OrderedSimplexEndpointFiber.freeSimplexRowIso W 0).hom) ≫
            (OrderedSimplexEndpointFiber.freeSimplexRowIso W 0).inv := by
              simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = _ := by rw [h, Category.assoc]
  calc
    _ = (OrderedSimplexEndpointFiber.freeSimplexRowIso W 1).inv ≫
          diagramMappingPrecomp
            (F.map (pointAt (single 1) (ULift.up i)) ≫
              F.map (singleIso 1).hom) W := by
            simp only [edgeLabelFromRow, Category.assoc,
              diagramMappingPrecomp_comp]
    _ = (OrderedSimplexEndpointFiber.freeSimplexRowIso W 1).inv ≫
          diagramMappingPrecomp
            (SegalRepresentables.freeSimplices.map
              (JTXiEndpointCollapseBoundary.ordinaryEndpoint i)) W := by
            rw [nativeEndpoint_coface]
    _ = JTProjectiveOrderedFiberComparison.endpoint W i ≫
          jointLabelFromRow W := by
            rw [h']
            simp only [jointLabelFromRow, Iso.inv_hom_id_assoc]

theorem jointLabelFromRow_vertex
    (x : (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)) :
    JTProjectiveOrderedFiberComparison.vertexPoint W x ≫ jointLabelFromRow W =
      OrderedNecklaceVertexPoints.zeroPoint W x := by
  rw [← OrderedSimplexEndpointFiber.freeSimplexRowIso_zeroPoint W x]
  simp only [jointLabelFromRow, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

def leftJoint : edgeLabels W ⟶ jointLabels W :=
  diagramMappingPrecomp
    (F.map (pointAt (single 1) (ULift.up (Fin.last 1)))) W

def rightJoint : edgeLabels W ⟶ jointLabels W :=
  diagramMappingPrecomp (F.map (pointAt (single 1) (ULift.up 0))) W

theorem edgeLabelFromRow_leftJoint :
    edgeLabelFromRow W ≫ leftJoint W =
      JTProjectiveOrderedFiberComparison.endpoint W 1 ≫ jointLabelFromRow W := by
  simpa only [leftJoint] using edgeLabelFromRow_endpoint W 1

theorem edgeLabelFromRow_rightJoint :
    edgeLabelFromRow W ≫ rightJoint W =
      JTProjectiveOrderedFiberComparison.endpoint W 0 ≫ jointLabelFromRow W := by
  simpa only [rightJoint] using edgeLabelFromRow_endpoint W 0

/-- Strict mapping spaces turn the actual free two-bead pushout into a pullback. -/
def wedgeMappingPullback :
    IsPullback
      (diagramMappingPrecomp (F.map (wedgeιLeft (single 1) (single 1))) W)
      (diagramMappingPrecomp (F.map (wedgeιRight (single 1) (single 1))) W)
      (leftJoint W) (rightJoint W) :=
  diagramMappingSpace_isPullback
    (ReversalDiscreteFreeColimits.map_isPushout
      (wedgeIsPushout (single 1) (single 1))) W

/-- Glue TWO complete Δ[1]-edge-label families over the SAME joint family. -/
def wedgeLabelMap (left right : K ⟶ edgeLabels W)
    (joint : left ≫ leftJoint W = right ≫ rightJoint W) :
    K ⟶ twoBeadLabels W :=
  (wedgeMappingPullback W).lift left right joint

theorem wedgeLabelMap_left (left right : K ⟶ edgeLabels W)
    (joint : left ≫ leftJoint W = right ≫ rightJoint W) :
    wedgeLabelMap W left right joint ≫
        diagramMappingPrecomp (F.map (wedgeιLeft (single 1) (single 1))) W =
      left :=
  (wedgeMappingPullback W).lift_fst left right joint

theorem wedgeLabelMap_right (left right : K ⟶ edgeLabels W)
    (joint : left ≫ leftJoint W = right ≫ rightJoint W) :
    wedgeLabelMap W left right joint ≫
        diagramMappingPrecomp (F.map (wedgeιRight (single 1) (single 1))) W =
      right :=
  (wedgeMappingPullback W).lift_snd left right joint

/-- The first vertex of the wedge is the first vertex of its left edge. -/
private theorem firstVertex_wedge :
    pointAt (single 1) (ULift.up 0) ≫
        wedgeιLeft (single 1) (single 1) =
      SSet.yonedaEquiv.symm T.first := by
  apply SSet.yonedaEquiv.injective
  simpa only [SSet.yonedaEquiv_comp, pointAt_vertex,
    Equiv.apply_symm_apply, first] using
    (wedgeιLeft_first (single 1) (single 1))

/-- The last vertex of the wedge is the last vertex of its right edge. -/
private theorem lastVertex_wedge :
    pointAt (single 1) (ULift.up (Fin.last 1)) ≫
        wedgeιRight (single 1) (single 1) =
      SSet.yonedaEquiv.symm T.last := by
  apply SSet.yonedaEquiv.injective
  simpa only [SSet.yonedaEquiv_comp, pointAt_vertex,
    Equiv.apply_symm_apply, last] using
    (wedgeιRight_last (single 1) (single 1))

private theorem boundaryRestriction_first :
    (necklaceBoundaryRestriction W).app (op T) ≫
        diagramMappingPrecomp
          (coprod.inl : F.obj (Δ[0] : SSet.{0}) ⟶ boundary) W =
      diagramMappingPrecomp (F.map (wedgeιLeft (single 1) (single 1))) W ≫
        diagramMappingPrecomp (F.map (pointAt (single 1) (ULift.up 0))) W := by
  change diagramMappingPrecomp (boundaryNecklace T) W ≫
      diagramMappingPrecomp coprod.inl W = _
  rw [← diagramMappingPrecomp_comp, ← diagramMappingPrecomp_comp]
  simp only [boundaryNecklace, coprod.inl_desc]
  rw [← Functor.map_comp, firstVertex_wedge]

private theorem boundaryRestriction_last :
    (necklaceBoundaryRestriction W).app (op T) ≫
        diagramMappingPrecomp
          (coprod.inr : F.obj (Δ[0] : SSet.{0}) ⟶ boundary) W =
      diagramMappingPrecomp (F.map (wedgeιRight (single 1) (single 1))) W ≫
        diagramMappingPrecomp
          (F.map (pointAt (single 1) (ULift.up (Fin.last 1)))) W := by
  change diagramMappingPrecomp (boundaryNecklace T) W ≫
      diagramMappingPrecomp coprod.inr W = _
  rw [← diagramMappingPrecomp_comp, ← diagramMappingPrecomp_comp]
  simp only [boundaryNecklace, coprod.inr_desc]
  rw [← Functor.map_comp, lastVertex_wedge]

/-- The two outer-endpoint equations imply the WHOLE ordered boundary equation. -/
theorem wedgeLabelMap_boundary
    (x y : (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌))
    (left right : K ⟶ edgeLabels W)
    (joint : left ≫ leftJoint W = right ≫ rightJoint W)
    (leftOuter : left ≫ diagramMappingPrecomp
        (F.map (pointAt (single 1) (ULift.up 0))) W =
      SSet.stdSimplex.isTerminalObj₀.from K ≫
        OrderedNecklaceVertexPoints.zeroPoint W x)
    (rightOuter : right ≫ diagramMappingPrecomp
        (F.map (pointAt (single 1) (ULift.up (Fin.last 1)))) W =
      SSet.stdSimplex.isTerminalObj₀.from K ≫
        OrderedNecklaceVertexPoints.zeroPoint W y) :
    wedgeLabelMap W left right joint ≫
        (necklaceBoundaryRestriction W).app (op T) =
      SSet.stdSimplex.isTerminalObj₀.from K ≫
        OrderedNecklaceVertexPoints.boundaryPoint W x y := by
  apply (cancel_mono (OrderedNecklaceVertexPoints.boundaryMappingIso W).hom).mp
  apply prod.hom_ext
  · simp only [Category.assoc,
      OrderedNecklaceVertexPoints.boundaryMappingIso_fst]
    calc
      _ = (wedgeLabelMap W left right joint ≫
          diagramMappingPrecomp (F.map (wedgeιLeft (single 1) (single 1))) W) ≫
            diagramMappingPrecomp (F.map (pointAt (single 1) (ULift.up 0))) W := by
              rw [Category.assoc, boundaryRestriction_first]
      _ = left ≫ diagramMappingPrecomp
            (F.map (pointAt (single 1) (ULift.up 0))) W := by
              rw [wedgeLabelMap_left]
      _ = SSet.stdSimplex.isTerminalObj₀.from K ≫
            OrderedNecklaceVertexPoints.zeroPoint W x := leftOuter
      _ = _ := by rw [OrderedNecklaceVertexPoints.boundaryPoint_first]
  · simp only [Category.assoc,
      OrderedNecklaceVertexPoints.boundaryMappingIso_snd]
    calc
      _ = (wedgeLabelMap W left right joint ≫
          diagramMappingPrecomp (F.map (wedgeιRight (single 1) (single 1))) W) ≫
            diagramMappingPrecomp
              (F.map (pointAt (single 1) (ULift.up (Fin.last 1)))) W := by
                rw [Category.assoc, boundaryRestriction_last]
      _ = right ≫ diagramMappingPrecomp
            (F.map (pointAt (single 1) (ULift.up (Fin.last 1)))) W := by
              rw [wedgeLabelMap_right]
      _ = SSet.stdSimplex.isTerminalObj₀.from K ≫
            OrderedNecklaceVertexPoints.zeroPoint W y := rightOuter
      _ = _ := by rw [OrderedNecklaceVertexPoints.boundaryPoint_last]

/-- A full degree-one ordered label at the ORIGINAL two raw vertices.
The boundary premise is an equality of entire Δ[1]-families. -/
def orderedWedgePoint
    (x y : (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌))
    (left right : K ⟶ edgeLabels W)
    (joint : left ≫ leftJoint W = right ≫ rightJoint W)
    (boundaryEq : wedgeLabelMap W left right joint ≫
        (necklaceBoundaryRestriction W).app (op T) =
      SSet.stdSimplex.isTerminalObj₀.from K ≫
        OrderedNecklaceVertexPoints.boundaryPoint W x y) :
    ((orderedNecklaceLabels W (OrderedNecklaceVertexPoints.boundaryPoint W x y)).obj
      (op T)).obj (op ⦋1⦌) :=
  SSet.yonedaEquiv (pullback.lift (wedgeLabelMap W left right joint)
    (SSet.stdSimplex.isTerminalObj₀.from K) boundaryEq)

/-- A degree-one ordered label from the two complete edge families and
their three endpoint equations, without a separate boundary premise. -/
def orderedWedgePointOfOuterEndpoints
    (x y : (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌))
    (left right : K ⟶ edgeLabels W)
    (joint : left ≫ leftJoint W = right ≫ rightJoint W)
    (leftOuter : left ≫ diagramMappingPrecomp
        (F.map (pointAt (single 1) (ULift.up 0))) W =
      SSet.stdSimplex.isTerminalObj₀.from K ≫
        OrderedNecklaceVertexPoints.zeroPoint W x)
    (rightOuter : right ≫ diagramMappingPrecomp
        (F.map (pointAt (single 1) (ULift.up (Fin.last 1)))) W =
      SSet.stdSimplex.isTerminalObj₀.from K ≫
        OrderedNecklaceVertexPoints.zeroPoint W y) :
    ((orderedNecklaceLabels W (OrderedNecklaceVertexPoints.boundaryPoint W x y)).obj
      (op T)).obj (op ⦋1⦌) :=
  orderedWedgePoint W x y left right joint
    (wedgeLabelMap_boundary W x y left right joint leftOuter rightOuter)

/-- Input in the ORIGINAL row-one space. Each hypothesis is an equality of
entire Δ[1]-families, so this construction can receive the normalized
J[1]-families only AFTER restricting along the actual simplex unit. -/
def orderedWedgePointFromRow
    (x y : (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌))
    (left right : K ⟶ JTProjectiveOrderedFiberComparison.row W ⦋1⦌)
    (joint : left ≫ JTProjectiveOrderedFiberComparison.endpoint W 1 =
      right ≫ JTProjectiveOrderedFiberComparison.endpoint W 0)
    (leftOuter : left ≫ JTProjectiveOrderedFiberComparison.endpoint W 0 =
      SSet.stdSimplex.isTerminalObj₀.from K ≫
        JTProjectiveOrderedFiberComparison.vertexPoint W x)
    (rightOuter : right ≫ JTProjectiveOrderedFiberComparison.endpoint W 1 =
      SSet.stdSimplex.isTerminalObj₀.from K ≫
        JTProjectiveOrderedFiberComparison.vertexPoint W y) :
    ((orderedNecklaceLabels W (OrderedNecklaceVertexPoints.boundaryPoint W x y)).obj
      (op T)).obj (op ⦋1⦌) := by
  let l := left ≫ edgeLabelFromRow W
  let r := right ≫ edgeLabelFromRow W
  have hj : l ≫ leftJoint W = r ≫ rightJoint W := by
    dsimp only [l, r]
    simp only [Category.assoc, edgeLabelFromRow_leftJoint,
      edgeLabelFromRow_rightJoint]
    exact congrArg (fun q => q ≫ jointLabelFromRow W) joint
  have hl : l ≫ diagramMappingPrecomp
      (F.map (pointAt (single 1) (ULift.up 0))) W =
      SSet.stdSimplex.isTerminalObj₀.from K ≫
        OrderedNecklaceVertexPoints.zeroPoint W x := by
    dsimp only [l]
    rw [Category.assoc, edgeLabelFromRow_endpoint W 0]
    have h := congrArg (fun q => q ≫ jointLabelFromRow W) leftOuter
    simpa only [Category.assoc, jointLabelFromRow_vertex] using h
  have hr : r ≫ diagramMappingPrecomp
      (F.map (pointAt (single 1) (ULift.up (Fin.last 1)))) W =
      SSet.stdSimplex.isTerminalObj₀.from K ≫
        OrderedNecklaceVertexPoints.zeroPoint W y := by
    dsimp only [r]
    change right ≫ edgeLabelFromRow W ≫ diagramMappingPrecomp
      (F.map (pointAt (single 1) (ULift.up (1 : Fin 2)))) W = _
    rw [edgeLabelFromRow_endpoint W 1]
    have h := congrArg (fun q => q ≫ jointLabelFromRow W) rightOuter
    simpa only [Category.assoc, jointLabelFromRow_vertex] using h
  exact orderedWedgePointOfOuterEndpoints W x y l r hj hl hr

end

end DaggerModels.PartII.TwoBeadEndpointLabel
