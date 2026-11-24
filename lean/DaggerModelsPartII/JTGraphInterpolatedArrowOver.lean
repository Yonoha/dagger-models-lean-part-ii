import DaggerModelsPartII.JTGraphInterpolatedOverOriginalSlice
import DaggerModelsPartII.JTGraphRestrictionNaturality

/-!
# Comparing the two graph lifts along one original comma arrow
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphInterpolatedArrowOver

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphLiftTransport (GraphLift)
open JTGraphLiftRestriction (restrict)
open JTGraphInterpolatedComparison (Fiber sliceObject)
open JTGraphInterpolatedOverOriginal (overOriginal)
open JTGraphInterpolatedOverOriginalSlice (overOriginal_slice_iso)
open JTGraphTransportNaturality (toComma)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {U V : TargetComma Q} (a : U ⟶ V)
variable (D : GraphLift U.left U.left.fiber.left) (E : GraphLift V.left V.left.fiber.left)
variable (hD : D.collapse = 𝟙 _) (hE : E.collapse = 𝟙 _)

/-- The transported source lift and the restricted target lift on the
original native source of the arrow. -/
def edgeFamily : Fin (⦋1⦌.len + 1) → GraphLift V.left U.left.fiber.left :=
  Fin.cases (D.transport a.left) (fun _ ↦ restrict E a.left.fiber.left)

include hD hE in
theorem edgeFamily_collapse (i : Fin (⦋1⦌.len + 1)) :
    (edgeFamily a D E i).collapse = a.left.fiber.left := by
  refine Fin.cases ?_ (fun _ ↦ ?_) i
  · change D.collapse ≫ a.left.fiber.left = a.left.fiber.left
    rw [hD, Category.id_comp]
  · change a.left.fiber.left ≫ E.collapse = a.left.fiber.left
    rw [hE, Category.comp_id]

/-- The entire degree-one comparison over the original target of the arrow. -/
def comparisonOverArrow : Fiber U.left.fiber.left ⦋1⦌ ⥤ Over V :=
  overOriginal a.left.fiber.left (edgeFamily a D E) (edgeFamily_collapse a D E hD hE)

/-- The first slice uses transport along the original comma arrow. -/
def transportedSliceIso :
    (comparisonOverArrow a D E hD hE).obj (sliceObject U.left.fiber.left ⦋1⦌ 0) ≅
      Over.mk (toComma (D.transport a.left)) :=
  overOriginal_slice_iso a.left.fiber.left (edgeFamily a D E)
    (edgeFamily_collapse a D E hD hE) 0

/-- The second slice uses restriction along the original native source map. -/
def restrictedSliceIso :
    (comparisonOverArrow a D E hD hE).obj (sliceObject U.left.fiber.left ⦋1⦌ 1) ≅
      Over.mk (toComma (restrict E a.left.fiber.left)) :=
  overOriginal_slice_iso a.left.fiber.left (edgeFamily a D E)
    (edgeFamily_collapse a D E hD hE) 1

end

end DaggerModels.PartII.JTGraphInterpolatedArrowOver
