import DaggerModelsPartII.JTMixedGraphHorizontalLabel
import DaggerModelsPartII.JTMixedGraphEdgeFamilyReindex
import DaggerModelsPartII.OrderedLabelElements

/-!
# Simultaneous horizontal and parameter transport of mixed graph ordered labels

Both operators act on the original ordered label, with no injectivity or
parameter-time hypothesis on the coefficient operator.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTMixedGraphOrderedLabelTransport

open JTProjectiveOrderedFiberComparison JTMixedGraphEndpointLifts
open JTMixedGraphHorizontalTraversal JTMixedGraphEdgeFamilyReindex

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Δ (k : SimplexCategory) := SSet.stdSimplex.{0}.obj k
private abbrev J (k : SimplexCategory) := GroupoidSimplex.parameter.obj k
private abbrev rows (W : Source) :=
  JTRealizationDiagonal.ordinaryCurry.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev labels (W : Source) (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) :=
  OrderedNecklaceLabelDiagram.orderedNecklaceLabels W
    (OrderedNecklaceVertexPoints.boundaryPoint W x y)

/-- The exact original ordered point transports along both the horizontal
operator and an arbitrary coefficient operator. -/
theorem orderedPoint_mixed_reindex {W : Source} {d e : ℕ}
    {k l : SimplexCategory} (a : ⦋d⦌ ⟶ ⦋e⦌)
    (h₀ : a.toOrderHom 0 = 0)
    (h₁ : a.toOrderHom (Fin.last d) = Fin.last e)
    (v : k ⟶ l)
    {f : Δ k ⟶ row W ⦋d⦌} {s : Δ ⦋d⦌ ⟶ J k}
    {g : Δ l ⟶ row W ⦋e⦌} {t : Δ ⦋e⦌ ⟶ J l}
    {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
    (E : EdgeFamilies W ⦋d⦌ k f s x y)
    (F : EdgeFamilies W ⦋e⦌ l g t x y)
    (hleft : E.left = SSet.stdSimplex.map v ≫ F.left)
    (hmiddle : f = SSet.stdSimplex.map v ≫ g ≫ (rows W).map a.op)
    (hright : E.right = SSet.stdSimplex.map v ≫ F.right) :
    JTMixedGraphOrderedLabel.orderedPoint E =
      ((labels W x y).obj
        (op (TripleBeadEndpointLabel.code d))).map v.op
        (((labels W x y).map
          (padded (singleOperator a h₀ h₁)).op).app (op l)
          (JTMixedGraphOrderedLabel.orderedPoint F)) := by
  let B := restrictFamilies a h₀ h₁ F
  have hcoeff : JTMixedGraphOrderedLabel.orderedPoint E =
      ((labels W x y).obj (op (TripleBeadEndpointLabel.code d))).map v.op
        (JTMixedGraphOrderedLabel.orderedPoint B) := by
    apply orderedPoint_reindex_of_rows v
      (JTMixedGraphOrderedLabel.families B)
      (JTMixedGraphOrderedLabel.families E)
    · change E.left ≫ TwoBeadEndpointLabel.edgeLabelFromRow W =
        SSet.stdSimplex.map v ≫ F.left ≫ TwoBeadEndpointLabel.edgeLabelFromRow W
      rw [hleft, Category.assoc]
    · change f ≫ JTNativeRowLabel.labelFromRow W d =
        SSet.stdSimplex.map v ≫
          (g ≫ (rows W).map a.op) ≫ JTNativeRowLabel.labelFromRow W d
      rw [hmiddle]
      simp only [Category.assoc]
    · change E.right ≫ TwoBeadEndpointLabel.edgeLabelFromRow W =
        SSet.stdSimplex.map v ≫ F.right ≫ TwoBeadEndpointLabel.edgeLabelFromRow W
      rw [hright, Category.assoc]
  rw [hcoeff]
  exact congrArg
    (((labels W x y).obj (op (TripleBeadEndpointLabel.code d))).map v.op)
    (JTMixedGraphHorizontalLabel.orderedPoint_horizontal a h₀ h₁ F).symm

/-- The same equation, expressed as one arrow of the joint ordered-label
presheaf on necklace codes and parameter simplices. -/
theorem orderedPoint_mixed_reindex_joint {W : Source} {d e : ℕ}
    {k l : SimplexCategory} (a : ⦋d⦌ ⟶ ⦋e⦌)
    (h₀ : a.toOrderHom 0 = 0)
    (h₁ : a.toOrderHom (Fin.last d) = Fin.last e)
    (v : k ⟶ l)
    {f : Δ k ⟶ row W ⦋d⦌} {s : Δ ⦋d⦌ ⟶ J k}
    {g : Δ l ⟶ row W ⦋e⦌} {t : Δ ⦋e⦌ ⟶ J l}
    {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
    (E : EdgeFamilies W ⦋d⦌ k f s x y)
    (F : EdgeFamilies W ⦋e⦌ l g t x y)
    (hleft : E.left = SSet.stdSimplex.map v ≫ F.left)
    (hmiddle : f = SSet.stdSimplex.map v ≫ g ≫ (rows W).map a.op)
    (hright : E.right = SSet.stdSimplex.map v ≫ F.right) :
    JTMixedGraphOrderedLabel.orderedPoint E =
      (OrderedLabelElements.labelPresheaf W
        (OrderedNecklaceVertexPoints.boundaryPoint W x y)).map
        (show (TripleBeadEndpointLabel.code d, k) ⟶
          (TripleBeadEndpointLabel.code e, l) from
          (padded (singleOperator a h₀ h₁), v)).op
        (JTMixedGraphOrderedLabel.orderedPoint F) := by
  exact orderedPoint_mixed_reindex a h₀ h₁ v E F hleft hmiddle hright

end

end DaggerModels.PartII.JTMixedGraphOrderedLabelTransport
