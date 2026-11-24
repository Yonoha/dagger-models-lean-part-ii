import DaggerModelsPartII.JTWhiskeredMiddleRestriction
import DaggerModelsPartII.JTSeamNativeCoefficients

/-! A triangle removes a seam detour after attaching the actual surrounding labels. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTWhiskeredSeamSpan

open JTThreePieceLabelOperators (Data index)
open JTWhiskeredMiddleRestriction (pullMiddle pullMiddleMap descendMiddle descendMiddleMap)
open JTSeamNativeCoefficients (spine longEdge collapseIdentity)
open JTProjectiveOrderedFiberComparison (row)
open JTNativeRowLabel (labelFromRow)
open TripleBeadEndpointLabel (glue)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev std := SSet.stdSimplex.{0}
private abbrev Rows (W : Source) :=
  JTRealizationDiagonal.ordinaryCurry.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev E := single 1

variable {W : Source} {P R : NecklaceCode} {k : SimplexCategory} {x y : Vertex W}
variable (D : Data W P (single 2) R k x y)
variable (τ : std.obj k ⟶ row W ⦋2⦌) (hD : D.middle = τ ≫ labelFromRow W 2)

/-- The two-edge detour with the SAME full surrounding coefficients. -/
abbrev detour := pullMiddle D spine

/-- The long edge with those identical surrounding coefficients and global endpoints. -/
abbrev long := pullMiddle D longEdge

/-- The first actual decorated leg of the detour/triangle/long-edge span. -/
def detourToTriangle : index (detour D) ⟶ index D := pullMiddleMap D spine

/-- The second actual decorated leg uses the triangle's genuine long native edge. -/
def longToTriangle : index (long D) ⟶ index D := pullMiddleMap D longEdge

include hD in
/-- The detour coefficient is exactly the two prescribed short-edge labels. -/
theorem detour_middle (e s : std.obj k ⟶ row W ⦋1⦌)
    (he : τ ≫ (Rows W).map (SimplexCategory.δ 2).op = e)
    (hs : τ ≫ (Rows W).map (SimplexCategory.δ 0).op = s)
    (hjoin : (e ≫ labelFromRow W 1) ≫ TripleBeadEndpointLabel.lastRestriction W E =
      (s ≫ labelFromRow W 1) ≫ TripleBeadEndpointLabel.firstRestriction W E) :
    (detour D).middle = glue W E E k (e ≫ labelFromRow W 1) (s ≫ labelFromRow W 1) hjoin := by
  change D.middle ≫ _ = _
  rw [hD]
  exact (JTSeamNativeCoefficients.triangle_spine W τ e s he hs hjoin).symm

variable (f : std.obj k ⟶ row W ⦋0⦌)
variable (hτ : τ ≫ (Rows W).map (SimplexCategory.δ 1).op =
  f ≫ JTEndpointNormalizationLifts.identityFamily W)

include hD hτ in
/-- The triangle's long edge is the identity at the VARYING original seam row. -/
theorem long_middle : (long D).middle =
    (f ≫ JTEndpointNormalizationLifts.identityFamily W) ≫ labelFromRow W 1 := by
  change D.middle ≫ _ = _
  rw [hD, JTSeamNativeCoefficients.triangle_long, hτ]

/-- Descend that identity edge to the original row vertex; surrounding native
pieces and the original coefficient degree remain unchanged. -/
def collapsed : Data W P (single 0) R k x y :=
  descendMiddle (long D) collapseIdentity (f ≫ labelFromRow W 0)
    ((long_middle D τ hD f hτ).trans (JTSeamNativeCoefficients.identity_coefficient W f))

/-- The last decorated leg collapses the identity, giving the complete span
 detour -> triangle <- identity -> vertex with fixed GLOBAL endpoints. -/
def longToCollapsed : index (long D) ⟶ index (collapsed D τ hD f hτ) :=
  descendMiddleMap (long D) collapseIdentity (f ≫ labelFromRow W 0)
    ((long_middle D τ hD f hτ).trans (JTSeamNativeCoefficients.identity_coefficient W f))

/-- All three comparisons keep the original coefficient degree literally fixed. -/
theorem detourToTriangle_projection :
    (OrderedLabelElements.projection W (OrderedNecklaceVertexPoints.boundaryPoint W x y)).map
      (detourToTriangle D) = (wedgeMap (𝟙 P) (wedgeMap spine (𝟙 R)), 𝟙 k) := rfl

theorem longToTriangle_projection :
    (OrderedLabelElements.projection W (OrderedNecklaceVertexPoints.boundaryPoint W x y)).map
      (longToTriangle D) = (wedgeMap (𝟙 P) (wedgeMap longEdge (𝟙 R)), 𝟙 k) := rfl

theorem longToCollapsed_projection :
    (OrderedLabelElements.projection W (OrderedNecklaceVertexPoints.boundaryPoint W x y)).map
      (longToCollapsed D τ hD f hτ) =
        (wedgeMap (𝟙 P) (wedgeMap collapseIdentity (𝟙 R)), 𝟙 k) := rfl

end
end DaggerModels.PartII.JTWhiskeredSeamSpan
