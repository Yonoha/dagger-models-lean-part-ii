import DaggerModelsPartII.JTMixedGraphEndpointLifts
import DaggerModelsPartII.JTNativeRowLabel
import DaggerModelsPartII.TripleBeadEndpointLabel
import DaggerModelsPartII.JTIdentityRowRealization

/-!
# The actual mixed graph gives a complete ordered three-bead label

The left and right original endpoint-normalizing row families are joined to
the unchanged central row coefficient. All three labels use the original
`Δ[k]` parameter, and their two joints and outer ordered boundary hold as
whole maps. The designated outer faces are the original identity-edge labels.
No target comparison, finality, or raw chosen-fiber weakness is asserted.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTMixedGraphOrderedLabel

open JTProjectiveOrderedFiberComparison JTMixedGraphEndpointLifts
open TripleBeadEndpointLabel

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Δ (k : SimplexCategory) := SSet.stdSimplex.{0}.obj k
private abbrev J (k : SimplexCategory) := GroupoidSimplex.parameter.obj k

variable {W : Source} {d : ℕ} {k : SimplexCategory}
variable {f : Δ k ⟶ row W ⦋d⦌} {s : Δ ⦋d⦌ ⟶ J k}
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (e : EdgeFamilies W ⦋d⦌ k f s x y)

private theorem left_middle_row_joint :
    e.left ≫ endpoint W 1 = f ≫ rowVertex W ⦋d⦌ 0 := by
  have h := congrArg (fun q ↦ q ≫ prod.snd) e.left_boundary
  simpa only [Category.assoc, endpointArrow, prod.lift_snd] using h

private theorem middle_right_row_joint :
    f ≫ rowVertex W ⦋d⦌ (Fin.last d) = e.right ≫ endpoint W 0 := by
  have h := congrArg (fun q ↦ q ≫ prod.fst) e.right_boundary
  simpa only [Category.assoc, endpointArrow, prod.lift_fst] using h.symm

private theorem left_outer_row :
    e.left ≫ endpoint W 0 =
      SSet.stdSimplex.isTerminalObj₀.from (Δ k) ≫ vertexPoint W x := by
  have h := congrArg (fun q ↦ q ≫ prod.fst) e.left_boundary
  simpa only [Category.assoc, endpointArrow, prod.lift_fst] using h

private theorem right_outer_row :
    e.right ≫ endpoint W 1 =
      SSet.stdSimplex.isTerminalObj₀.from (Δ k) ≫ vertexPoint W y := by
  have h := congrArg (fun q ↦ q ≫ prod.snd) e.right_boundary
  simpa only [Category.assoc, endpointArrow, prod.lift_snd] using h

/-- The complete three native bead labels, with the unchanged original
boundary point `boundaryPoint W x y` supplied by the generic triple module. -/
def families : TripleBeadEndpointLabel.Families W d k x y where
  left := e.left ≫ TwoBeadEndpointLabel.edgeLabelFromRow W
  middle := f ≫ JTNativeRowLabel.labelFromRow W d
  right := e.right ≫ TwoBeadEndpointLabel.edgeLabelFromRow W
  leftJoint := by
    change (e.left ≫ TwoBeadEndpointLabel.edgeLabelFromRow W) ≫
        TwoBeadEndpointLabel.leftJoint W =
      (f ≫ JTNativeRowLabel.labelFromRow W d) ≫
        diagramMappingPrecomp
          (ReversalDiscreteFreeColimits.discreteFree.map
            (pointAt (single d) (ULift.up 0))) W
    simp only [Category.assoc, TwoBeadEndpointLabel.edgeLabelFromRow_leftJoint,
      JTNativeRowLabel.labelFromRow_vertex]
    exact congrArg (fun q ↦ q ≫ TwoBeadEndpointLabel.jointLabelFromRow W)
      (left_middle_row_joint e)
  rightJoint := by
    change (f ≫ JTNativeRowLabel.labelFromRow W d) ≫
        diagramMappingPrecomp
          (ReversalDiscreteFreeColimits.discreteFree.map
            (pointAt (single d) (ULift.up (Fin.last d)))) W =
      (e.right ≫ TwoBeadEndpointLabel.edgeLabelFromRow W) ≫
        TwoBeadEndpointLabel.rightJoint W
    simp only [Category.assoc, TwoBeadEndpointLabel.edgeLabelFromRow_rightJoint,
      JTNativeRowLabel.labelFromRow_vertex]
    exact congrArg (fun q ↦ q ≫ TwoBeadEndpointLabel.jointLabelFromRow W)
      (middle_right_row_joint e)
  firstOuter := by
    change (e.left ≫ TwoBeadEndpointLabel.edgeLabelFromRow W) ≫
        TwoBeadEndpointLabel.rightJoint W =
      SSet.stdSimplex.isTerminalObj₀.from (Δ k) ≫
        OrderedNecklaceVertexPoints.zeroPoint W x
    rw [Category.assoc, TwoBeadEndpointLabel.edgeLabelFromRow_rightJoint]
    have h := congrArg (fun q ↦ q ≫ TwoBeadEndpointLabel.jointLabelFromRow W)
      (left_outer_row e)
    simpa only [Category.assoc, TwoBeadEndpointLabel.jointLabelFromRow_vertex]
      using h
  lastOuter := by
    change (e.right ≫ TwoBeadEndpointLabel.edgeLabelFromRow W) ≫
        TwoBeadEndpointLabel.leftJoint W =
      SSet.stdSimplex.isTerminalObj₀.from (Δ k) ≫
        OrderedNecklaceVertexPoints.zeroPoint W y
    rw [Category.assoc, TwoBeadEndpointLabel.edgeLabelFromRow_leftJoint]
    have h := congrArg (fun q ↦ q ≫ TwoBeadEndpointLabel.jointLabelFromRow W)
      (right_outer_row e)
    simpa only [Category.assoc, TwoBeadEndpointLabel.jointLabelFromRow_vertex]
      using h

/-- The genuine original ordered-label element on the native three-bead code. -/
def orderedPoint :
    ((OrderedNecklaceLabelDiagram.orderedNecklaceLabels W
      (OrderedNecklaceVertexPoints.boundaryPoint W x y)).obj
        (op (TripleBeadEndpointLabel.code d))).obj (op k) :=
  TripleBeadEndpointLabel.orderedPoint (families e)

theorem orderedPoint_left :
    SSet.yonedaEquiv.symm
        (JTRealizedLabelEndpoints.orderedLabel W x y
          (TripleBeadEndpointLabel.code d) k (orderedPoint e)) ≫
      diagramMappingPrecomp
        (ReversalDiscreteFreeColimits.discreteFree.map
          (tripleRightT (single 1) (single d) (single 1))) W =
      e.left ≫ TwoBeadEndpointLabel.edgeLabelFromRow W :=
  TripleBeadEndpointLabel.orderedPoint_left (families e)

theorem orderedPoint_middle :
    SSet.yonedaEquiv.symm
        (JTRealizedLabelEndpoints.orderedLabel W x y
          (TripleBeadEndpointLabel.code d) k (orderedPoint e)) ≫
      diagramMappingPrecomp
        (ReversalDiscreteFreeColimits.discreteFree.map
          (tripleRightU (single 1) (single d) (single 1))) W =
      f ≫ JTNativeRowLabel.labelFromRow W d :=
  TripleBeadEndpointLabel.orderedPoint_middle (families e)

theorem orderedPoint_right :
    SSet.yonedaEquiv.symm
        (JTRealizedLabelEndpoints.orderedLabel W x y
          (TripleBeadEndpointLabel.code d) k (orderedPoint e)) ≫
      diagramMappingPrecomp
        (ReversalDiscreteFreeColimits.discreteFree.map
          (tripleRightV (single 1) (single d) (single 1))) W =
      e.right ≫ TwoBeadEndpointLabel.edgeLabelFromRow W :=
  TripleBeadEndpointLabel.orderedPoint_right (families e)

/-- The designated initial face of the left outer bead is precisely the
original degree-zero identity edge label at `x`. -/
theorem left_identity_face :
    (diagramTensor
        (ReversalDiscreteFreeColimits.discreteFree.obj (single 1).toSSet)).map
        (vertex k (graphIndex ⦋d⦌ k s 0)) ≫
      SSet.yonedaEquiv (e.left ≫ TwoBeadEndpointLabel.edgeLabelFromRow W) =
        JTIdentityRowRealization.identityEdgeLabel W x := by
  change (TripleBeadEndpointLabel.labels W (single 1)).map
      (SimplexCategory.const ⦋0⦌ k (graphIndex ⦋d⦌ k s 0)).op
      (SSet.yonedaEquiv (e.left ≫ TwoBeadEndpointLabel.edgeLabelFromRow W)) = _
  apply SSet.yonedaEquiv.symm.injective
  rw [← SSet.stdSimplex.map_comp_yonedaEquiv_symm]
  dsimp only [JTIdentityRowRealization.identityEdgeLabel]
  erw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  simpa only [vertex, Category.assoc] using
    congrArg (fun q ↦ q ≫ TwoBeadEndpointLabel.edgeLabelFromRow W)
      e.left_degenerate

/-- The designated terminal face of the right outer bead is precisely the
original degree-zero identity edge label at `y`. -/
theorem right_identity_face :
    (diagramTensor
        (ReversalDiscreteFreeColimits.discreteFree.obj (single 1).toSSet)).map
        (vertex k (graphIndex ⦋d⦌ k s (Fin.last d))) ≫
      SSet.yonedaEquiv (e.right ≫ TwoBeadEndpointLabel.edgeLabelFromRow W) =
        JTIdentityRowRealization.identityEdgeLabel W y := by
  change (TripleBeadEndpointLabel.labels W (single 1)).map
      (SimplexCategory.const ⦋0⦌ k (graphIndex ⦋d⦌ k s (Fin.last d))).op
      (SSet.yonedaEquiv (e.right ≫ TwoBeadEndpointLabel.edgeLabelFromRow W)) = _
  apply SSet.yonedaEquiv.symm.injective
  rw [← SSet.stdSimplex.map_comp_yonedaEquiv_symm]
  dsimp only [JTIdentityRowRealization.identityEdgeLabel]
  erw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  simpa only [vertex, Category.assoc] using
    congrArg (fun q ↦ q ≫ TwoBeadEndpointLabel.edgeLabelFromRow W)
      e.right_degenerate

end

end DaggerModels.PartII.JTMixedGraphOrderedLabel
