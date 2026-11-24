import DaggerModelsPartII.JTMixedGraphHorizontalLabel
import DaggerModelsPartII.JTOrderedLabelJointInsertion
import DaggerModelsPartII.JTEndpointNormalizationLifts

/-! Transfer a relative row-one lift to the actual native edge label. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTWhiskerEdgeCoefficient

open JTProjectiveOrderedFiberComparison (row endpoint vertexPoint)
open JTEndpointNormalizationLifts (identityFamily)
open TripleBeadEndpointLabel (firstRestriction lastRestriction)
open TwoBeadEndpointLabel (edgeLabelFromRow jointLabelFromRow jointLabelFromRow_vertex
  edgeLabelFromRow_endpoint)
open ReversalDiscreteFreeColimits OrderedNecklaceVertexPoints
open JTNativeRowLabel (labelFromRow)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev free := discreteFree.{0}

variable (W : Source) {k l : SimplexCategory}

set_option maxHeartbeats 700000 in
/-- A horizontally degenerate row-one coefficient gives the literal constant edge label. -/
theorem identityEdge (z : Vertex W) :
    (term (std.obj k) ≫ vertexPoint W z ≫ identityFamily W) ≫ edgeLabelFromRow W =
      JTConstantOrderedLabel.constantCoefficient W z (single 1) k := by
  let r := SimplexCategory.isTerminalZero.from ⦋1⦌
  let h₀ : r.toOrderHom 0 = 0 := @Subsingleton.elim (Fin 1) inferInstance _ _
  let h₁ : r.toOrderHom (Fin.last 1) = Fin.last 0 := @Subsingleton.elim (Fin 1) inferInstance _ _
  let c := JTMixedGraphHorizontalTraversal.singleOperator r h₀ h₁
  have h := JTMixedGraphHorizontalLabel.labelFromRow_natural W r h₀ h₁
  change labelFromRow W 0 ≫ diagramMappingPrecomp (free.map c.map) W =
    identityFamily W ≫ edgeLabelFromRow W at h
  have ht : c.map ≫ (singleIso 0).hom = term (single 1).toSSet :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have h' : identityFamily W ≫ edgeLabelFromRow W =
      jointLabelFromRow W ≫ diagramMappingPrecomp (free.map (term (single 1).toSSet)) W := by
    rw [← h]
    simp only [labelFromRow, jointLabelFromRow, Category.assoc, ← diagramMappingPrecomp_comp,
      ← free.map_comp, ht]
  simp only [Category.assoc]
  rw [h', ← Category.assoc (vertexPoint W z), jointLabelFromRow_vertex]
  rfl

/-- The first endpoint of a relative row lift is exactly its row-zero first endpoint. -/
theorem first (e : std.obj k ⟶ row W ⦋1⦌) :
    (e ≫ edgeLabelFromRow W) ≫ firstRestriction W (single 1) =
      (e ≫ endpoint W 0) ≫ jointLabelFromRow W := by
  simp only [Category.assoc]
  exact congrArg (fun f ↦ e ≫ f) (edgeLabelFromRow_endpoint W 0)

/-- The last endpoint of a relative row lift is exactly its row-zero last endpoint. -/
theorem last (e : std.obj k ⟶ row W ⦋1⦌) :
    (e ≫ edgeLabelFromRow W) ≫ lastRestriction W (single 1) =
      (e ≫ endpoint W 1) ≫ jointLabelFromRow W := by
  simp only [Category.assoc]
  exact congrArg (fun f ↦ e ≫ f) (edgeLabelFromRow_endpoint W 1)

/-- If the relative lift is the identity on the given face then the native label
on the whole face is the constant joint coefficient. -/
theorem onFace (u : l ⟶ k) (z : Vertex W) (e : std.obj k ⟶ row W ⦋1⦌)
    (h : std.map u ≫ e = term (std.obj l) ≫ vertexPoint W z ≫ identityFamily W) :
    std.map u ≫ (e ≫ edgeLabelFromRow W) =
      JTConstantOrderedLabel.constantCoefficient W z (single 1) l := by
  rw [← Category.assoc, h, identityEdge]

end
end DaggerModels.PartII.JTWhiskerEdgeCoefficient
