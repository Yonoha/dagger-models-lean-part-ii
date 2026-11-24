import DaggerModelsPartII.JTNativeRowCoefficientOperators
import DaggerModelsPartII.NecklaceSimplexCompletion
import DaggerModelsPartII.JTWhiskerEdgeCoefficient

/-! The two short edges, long edge and identity collapse of an actual seam triangle. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTSeamNativeCoefficients

open OrderedNecklaceLabelDiagram (completionUnitComponent completionEdgeComponent)
open JTNativeRowCoefficientOperators (nativeOperator coefficient_operator)
open JTProjectiveOrderedFiberComparison (row)
open JTNativeRowLabel (labelFromRow)
open TripleBeadEndpointLabel (labels glue glue_left glue_right wedgeMappingPullback)
open ReversalDiscreteFreeColimits (discreteFree)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev E := single 1
private abbrev std := SSet.stdSimplex.{0}
private abbrev Rows (W : Source) :=
  JTRealizationDiagonal.ordinaryCurry.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev pre (W : Source) {X Y : SSet.{0}} (i : X ⟶ Y) :=
  diagramMappingPrecomp (discreteFree.map i) W

/-- The original two-edge spine is a genuine endpoint-preserving native arrow. -/
abbrev spine : wedge E E ⟶ single 2 := completionUnitComponent (wedge E E)

/-- The original long edge is another genuine native arrow to that same triangle. -/
abbrev longEdge : E ⟶ single 2 := completionEdgeComponent (wedge E E)

/-- Its first short edge is exactly the ordinary face opposite vertex two. -/
theorem spine_left : wedgeιLeft E E ≫ spine.map = nativeOperator (SimplexCategory.δ 2) := by
  change wedgeιLeft E E ≫ ((wedge E E).inclusion ≫ (singleIso 2).inv) = _
  rw [← Category.assoc, wedgeιLeft_inclusion, ← singleIso_hom]
  have h : (SimplexCategory.Hom.mk (wedgeLeft E E).toOrderHom : ⦋1⦌ ⟶ ⦋2⦌) =
      SimplexCategory.δ 2 := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext v
    fin_cases v <;> rfl
  rw [h]
  rfl

/-- Its second short edge is the ordinary face opposite vertex zero. -/
theorem spine_right : wedgeιRight E E ≫ spine.map = nativeOperator (SimplexCategory.δ 0) := by
  change wedgeιRight E E ≫ ((wedge E E).inclusion ≫ (singleIso 2).inv) = _
  rw [← Category.assoc, wedgeιRight_inclusion, ← singleIso_hom]
  have h : (SimplexCategory.Hom.mk (wedgeRight E E).toOrderHom : ⦋1⦌ ⟶ ⦋2⦌) =
      SimplexCategory.δ 0 := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext v
    fin_cases v <;> rfl
  rw [h]
  rfl

/-- The long edge is exactly the ordinary face opposite vertex one. -/
theorem longEdge_map : longEdge.map = nativeOperator (SimplexCategory.δ 1) := by
  change (singleIso 1).hom ≫ DaggerOriginalProductGadget.edgeToAmbient (wedge E E) ≫
      (singleIso 2).inv = _
  have h : DaggerOriginalProductGadget.edgeToAmbient (wedge E E) =
      std.map (SimplexCategory.δ 1) := by
    unfold DaggerOriginalProductGadget.edgeToAmbient DaggerOriginalProductGadget.simplexEdge
    congr 1
    ext v : 3
    fin_cases v <;> rfl
  rw [h]
  rfl

variable (W : Source) {k : SimplexCategory}

/-- Restriction of the triangle label along its long native edge. -/
theorem triangle_long (τ : std.obj k ⟶ row W ⦋2⦌) :
    (τ ≫ labelFromRow W 2) ≫ pre W longEdge.map =
      (τ ≫ (Rows W).map (SimplexCategory.δ 1).op) ≫ labelFromRow W 1 := by
  rw [longEdge_map]
  exact coefficient_operator W _ τ

/-- Both prescribed short-edge coefficients determine the full spine restriction. -/
theorem triangle_spine (τ : std.obj k ⟶ row W ⦋2⦌)
    (e s : std.obj k ⟶ row W ⦋1⦌)
    (he : τ ≫ (Rows W).map (SimplexCategory.δ 2).op = e)
    (hs : τ ≫ (Rows W).map (SimplexCategory.δ 0).op = s)
    (hjoin : (e ≫ labelFromRow W 1) ≫ TripleBeadEndpointLabel.lastRestriction W E =
      (s ≫ labelFromRow W 1) ≫ TripleBeadEndpointLabel.firstRestriction W E) :
    glue W E E k (e ≫ labelFromRow W 1) (s ≫ labelFromRow W 1) hjoin =
      (τ ≫ labelFromRow W 2) ≫ pre W spine.map := by
  apply (wedgeMappingPullback W E E).hom_ext
  · rw [glue_left, Category.assoc, ← diagramMappingPrecomp_comp,
      ← discreteFree.map_comp, spine_left, coefficient_operator, he]
  · rw [glue_right, Category.assoc, ← diagramMappingPrecomp_comp,
      ← discreteFree.map_comp, spine_right, coefficient_operator, hs]

/-- Collapse of the inserted identity edge, keeping the varying old seam row. -/
def collapseIdentity : E ⟶ single 0 :=
  JTMixedGraphHorizontalTraversal.singleOperator (SimplexCategory.isTerminalZero.from ⦋1⦌)
    (@Subsingleton.elim (Fin 1) inferInstance _ _)
    (@Subsingleton.elim (Fin 1) inferInstance _ _)

/-- The horizontally degenerate edge is the native pullback of that same row vertex. -/
theorem identity_coefficient (f : std.obj k ⟶ row W ⦋0⦌) :
    (f ≫ JTEndpointNormalizationLifts.identityFamily W) ≫ labelFromRow W 1 =
      (f ≫ labelFromRow W 0) ≫ pre W collapseIdentity.map := by
  have h := JTMixedGraphHorizontalLabel.labelFromRow_natural W
    (SimplexCategory.isTerminalZero.from ⦋1⦌)
    (@Subsingleton.elim (Fin 1) inferInstance _ _)
    (@Subsingleton.elim (Fin 1) inferInstance _ _)
  change labelFromRow W 0 ≫ pre W collapseIdentity.map =
    JTEndpointNormalizationLifts.identityFamily W ≫ labelFromRow W 1 at h
  rw [Category.assoc, ← h, Category.assoc]

end
end DaggerModels.PartII.JTSeamNativeCoefficients
