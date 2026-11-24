import DaggerModelsPartII.JTChangingCoefficientBridgeFamilies

/-!
# Restriction of the whole ordered label across a change of coefficient
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTChangingCoefficientBridgeLabels

open JTChangingCoefficientBridgeOrder JTChangingCoefficientBridgePrism
open JTChangingCoefficientBridgeFamilies
open JTProjectiveOrderedFiberComparison JTMixedGraphEndpointLifts JTMixedGraphEdgeFamilyReindex
open OrderedNecklaceLabelDiagram OrderedNecklaceVertexPoints
open JTHigherInterleavedParameter (common)

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev simplex (k : SimplexCategory) := SSet.stdSimplex.{0}.obj k
private abbrev J := GroupoidSimplex.parameter

variable {W : Source} {d : ℕ} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {k b b' : SimplexCategory} (c : k ⟶ b) (h : b ⟶ b') (n : SimplexCategory)
variable (f : simplex b' ⟶ row W ⦋d⦌) (s : simplex ⦋d⦌ ⟶ J.obj k)
variable (E : EdgeFamilies W ⦋d⦌ (bridge k n) (SSet.stdSimplex.map (base c h n) ≫ f)
  (s ≫ J.map (slice c h n 0)) x y)

/-- The original three-bead label restricts exactly to the independently
prescribed one on each side. The middle row map restricts along the changed base. -/
theorem orderedPoint_side (e : Fin 2)
    (D : EdgeFamilies W ⦋d⦌ (common k n) (sideRow c h n f e)
      (s ≫ J.map (sideSlice c h n e)) x y)
    (hleft : SSet.stdSimplex.map (side c h n e) ≫ E.left = D.left)
    (hright : SSet.stdSimplex.map (side c h n e) ≫ E.right = D.right) :
    ((orderedNecklaceLabels W (boundaryPoint W x y)).obj
      (op (TripleBeadEndpointLabel.code d))).map (side c h n e).op
        (JTMixedGraphOrderedLabel.orderedPoint E) = JTMixedGraphOrderedLabel.orderedPoint D := by
  symm
  apply orderedPoint_reindex_of_rows (side c h n e)
    (JTMixedGraphOrderedLabel.families E) (JTMixedGraphOrderedLabel.families D)
  · dsimp only [JTMixedGraphOrderedLabel.families]
    rw [← Category.assoc, hleft]
  · dsimp only [JTMixedGraphOrderedLabel.families, sideRow]
    rw [Category.assoc]
  · dsimp only [JTMixedGraphOrderedLabel.families]
    rw [← Category.assoc, hright]

end DaggerModels.PartII.JTChangingCoefficientBridgeLabels
