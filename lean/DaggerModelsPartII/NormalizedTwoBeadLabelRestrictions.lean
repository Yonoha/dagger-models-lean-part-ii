import DaggerModelsPartII.NormalizedTwoBeadPresentation
import DaggerModelsPartII.JTRealizedLabelEndpoints
import DaggerModelsPartII.JTNecklaceLabelRealization

/-!
# Complete edge and joint restrictions of the normalized two-bead label

The actual ordered label recovers both entire Δ[1]-parameter edge families,
and its middle vertex recovers the same original zero-row family. These are
strict source-side equations; no raw realization-edge factorization, target
comma contraction, or chosen-fiber weakness is inferred.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.NormalizedTwoBeadLabelRestrictions

open ReversalDiscreteFreeColimits OrderedNecklaceLabelDiagram
open JTProjectiveOrderedFiberComparison JTEndpointNormalizationLifts

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev F := discreteFree.{0}
private abbrev T := TwoBeadCylinderTraversal.twoBead
private abbrev E := (single 1).toSSet
private abbrev J := GroupoidSimplex.parameter.obj ⦋1⦌

variable {W : Source} {z : J ⟶ row W ⦋0⦌}
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}

/-- The actual pullback first projection, retaining the SAME original label. -/
def η (d : Families W ⦋1⦌ 0 1 z x y) :
    (diagramMappingSpace (F.obj T.toSSet) W).obj (op ⦋1⦌) :=
  JTRealizedLabelEndpoints.orderedLabel W x y T ⦋1⦌
    (NormalizedTwoBeadPresentation.orderedLabel d)

/-- The complete left Δ[1]-family, before passing to a coefficient. -/
theorem left_family (d : Families W ⦋1⦌ 0 1 z x y) :
    SSet.yonedaEquiv.symm (η d) ≫
        diagramMappingPrecomp (F.map (wedgeιLeft (single 1) (single 1))) W =
      leftSimplexFamily d ≫ TwoBeadEndpointLabel.edgeLabelFromRow W := by
  dsimp only [η, JTRealizedLabelEndpoints.orderedLabel,
    NormalizedTwoBeadPresentation.orderedLabel,
    TwoBeadEndpointLabel.orderedWedgePointFromRow,
    TwoBeadEndpointLabel.orderedWedgePointOfOuterEndpoints,
    TwoBeadEndpointLabel.orderedWedgePoint]
  rw [← SSet.yonedaEquiv_symm_comp]
  erw [Equiv.symm_apply_apply]
  erw [pullback.lift_fst]
  exact TwoBeadEndpointLabel.wedgeLabelMap_left W _ _ _

/-- The complete right Δ[1]-family, before passing to a coefficient. -/
theorem right_family (d : Families W ⦋1⦌ 0 1 z x y) :
    SSet.yonedaEquiv.symm (η d) ≫
        diagramMappingPrecomp (F.map (wedgeιRight (single 1) (single 1))) W =
      rightSimplexFamily d ≫ TwoBeadEndpointLabel.edgeLabelFromRow W := by
  dsimp only [η, JTRealizedLabelEndpoints.orderedLabel,
    NormalizedTwoBeadPresentation.orderedLabel,
    TwoBeadEndpointLabel.orderedWedgePointFromRow,
    TwoBeadEndpointLabel.orderedWedgePointOfOuterEndpoints,
    TwoBeadEndpointLabel.orderedWedgePoint]
  rw [← SSet.yonedaEquiv_symm_comp]
  erw [Equiv.symm_apply_apply]
  erw [pullback.lift_fst]
  exact TwoBeadEndpointLabel.wedgeLabelMap_right W _ _ _

/-- The requested equality of complete strict labels on the left bead. -/
theorem left_coefficient (d : Families W ⦋1⦌ 0 1 z x y) :
    Functor.whiskerRight (F.map (wedgeιLeft (single 1) (single 1)))
        (tensorRight (Δ[1] : SSet.{0})) ≫ η d =
      SSet.yonedaEquiv
        (leftSimplexFamily d ≫ TwoBeadEndpointLabel.edgeLabelFromRow W) := by
  have h := congrArg SSet.yonedaEquiv (left_family d)
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at h
  change _ = _ at h
  exact h

/-- The requested equality of complete strict labels on the right bead. -/
theorem right_coefficient (d : Families W ⦋1⦌ 0 1 z x y) :
    Functor.whiskerRight (F.map (wedgeιRight (single 1) (single 1)))
        (tensorRight (Δ[1] : SSet.{0})) ≫ η d =
      SSet.yonedaEquiv
        (rightSimplexFamily d ≫ TwoBeadEndpointLabel.edgeLabelFromRow W) := by
  have h := congrArg SSet.yonedaEquiv (right_family d)
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at h
  change _ = _ at h
  exact h

/-- The left edge's terminal vertex is the native wedge's middle vertex. -/
private theorem left_joint_point :
    pointAt (single 1) (ULift.up (Fin.last 1)) ≫
        wedgeιLeft (single 1) (single 1) =
      pointAt T (ULift.up (1 : Fin (T.len + 1))) := by
  rw [pointAt_comp, wedgeιLeft_vertices]
  rfl

/-- The full middle-vertex family is precisely the originally specified
zero-row family after restriction along the actual simplex unit. -/
theorem joint_family (d : Families W ⦋1⦌ 0 1 z x y) :
    SSet.yonedaEquiv.symm (η d) ≫
        diagramMappingPrecomp
          (F.map (pointAt T (ULift.up (1 : Fin (T.len + 1))))) W =
      JTCylinderCEComparison.simplexUnit.app ⦋1⦌ ≫ z ≫
        TwoBeadEndpointLabel.jointLabelFromRow W := by
  have hpre : diagramMappingPrecomp
      (F.map (pointAt T (ULift.up (1 : Fin (T.len + 1))))) W =
      diagramMappingPrecomp (F.map (wedgeιLeft (single 1) (single 1))) W ≫
        TwoBeadEndpointLabel.leftJoint W := by
    rw [TwoBeadEndpointLabel.leftJoint, ← diagramMappingPrecomp_comp,
      ← Functor.map_comp, left_joint_point]
  have hmid := congrArg (fun q ↦ q ≫ prod.snd) (leftSimplex_boundary d)
  simp only [Category.assoc, endpointArrow, prod.lift_snd] at hmid
  calc
    _ = (SSet.yonedaEquiv.symm (η d) ≫
          diagramMappingPrecomp (F.map (wedgeιLeft (single 1) (single 1))) W) ≫
            TwoBeadEndpointLabel.leftJoint W := by
              rw [hpre, Category.assoc]
    _ = (leftSimplexFamily d ≫ TwoBeadEndpointLabel.edgeLabelFromRow W) ≫
          TwoBeadEndpointLabel.leftJoint W := by rw [left_family]
    _ = leftSimplexFamily d ≫ endpoint W 1 ≫
          TwoBeadEndpointLabel.jointLabelFromRow W := by
            rw [Category.assoc, TwoBeadEndpointLabel.edgeLabelFromRow_leftJoint]
    _ = _ := by rw [← Category.assoc, hmid, Category.assoc]

end

end DaggerModels.PartII.NormalizedTwoBeadLabelRestrictions
