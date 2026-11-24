import DaggerModelsPartII.JTChangingCoefficientBridgeCylinder
import DaggerModelsPartII.JTRowGraphPrismRaw

/-!
# The binary joining cylinder over the original raw target
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTChangingCoefficientBridgeRaw

open JTChangingCoefficientBridgeOrder JTChangingCoefficientBridgeTime
open JTChangingCoefficientBridgePrism JTChangingCoefficientBridgeCylinder
open JTChangingCoefficientBridgeGroupoid (paired paired_base paired_slice paired_vertex)
open OrdinaryJTRealization JTReversalInput JTProjectiveOrderedFiberComparison
open JTMixedGraphEndpointLifts JTMixedGraphRawRefinement
open MixedGraphCylinderTraversal JTNecklaceEndpointCylinder NecklaceCylinderAugmentation

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev R (W : Source) := realization.obj (ordinaryInput.obj W)
private abbrev J := GroupoidSimplex.parameter
private abbrev simplex (k : SimplexCategory) := SSet.stdSimplex.{0}.obj k
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {d : ℕ} {k b b' : SimplexCategory}
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (c : k ⟶ b) (h : b ⟶ b') (n : SimplexCategory)
variable (f : simplex b' ⟶ row W ⦋d⦌) (s : simplex ⦋d⦌ ⟶ J.obj k)
variable (E : EdgeFamilies W ⦋d⦌ (bridge k n) (SSet.stdSimplex.map (base c h n) ≫ f)
  (s ≫ J.map (slice c h n 0)) x y)

/-- The whole joining cylinder has the same original raw target map. -/
theorem whole_raw {q : (single d).toSSet ⟶ R W}
    (hq : nativeRawGraph W d k (SSet.stdSimplex.map (c ≫ h) ≫ f) s = q)
    (qx : q.app (op ⦋0⦌) (single d).first = rawVertex W x)
    (qy : q.app (op ⦋0⦌) (single d).last = rawVertex W y)
    (hL : SSet.stdSimplex.map (vertical c h n (graphIndex ⦋d⦌ k s 0)) ≫ E.left =
      term (simplex (time n)) ≫ vertexPoint W x ≫ JTEndpointNormalizationLifts.identityFamily W)
    (hR : SSet.stdSimplex.map (vertical c h n (graphIndex ⦋d⦌ k s (Fin.last d))) ≫ E.right =
      term (simplex (time n)) ≫ vertexPoint W y ≫ JTEndpointNormalizationLifts.identityFamily W) :
    cylinderMap c h n (code d) (nativeGraphParameter s) ≫
        descend W x y (code d) (bridge k n) (JTMixedGraphOrderedLabel.orderedPoint E) =
      augmentation (code d) (time n) ≫ (collapseOuter d).map ≫ q := by
  let D : JTRowGraphPrismRaw.PrismData k (time n) (bridge k n) b' :=
    { coefficient := c ≫ h
      base := base c h n
      slice := slice c h n 0
      vertical := vertical c h n
      slice_base := slice_base c h n 0
      paired := paired c h n
      paired_base := paired_base c h n
      paired_slice := paired_slice c h n 0
      paired_vertex := paired_vertex c h n }
  exact JTRowGraphPrismRaw.whole_raw D f s E hq qx qy hL hR
    (cylinderMap c h n (code d) (nativeGraphParameter s))
    (cylinderMap_cylinder c h n (code d) (nativeGraphParameter s))
    (cylinderMap_boundary c h n (code d) (nativeGraphParameter s))

end

end DaggerModels.PartII.JTChangingCoefficientBridgeRaw
