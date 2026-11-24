import DaggerModelsPartII.JTGraphTransportNaturality
import DaggerModelsPartII.JTGraphMultiBeadIdentityLift
import ChosenNecklaceWedgeUnits

/-! Graph predecessors obtained by appending degenerate terminal beads. -/

set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels DaggerChosenRigidificationNecklace
namespace DaggerModels.PartII.JTGraphLargePredecessor
open JTGraphLiftTransport
open JTProjectiveOrderedFiberComparison (row)
open NecklaceCode
noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

private def chain (n : ℕ) : NecklaceCode := ⟨n, Finset.univ, Finset.mem_univ _, Finset.mem_univ _⟩

private def chainToPoint (n : ℕ) : chain n ⟶ point where
  map := SSet.stdSimplex.isTerminalObj₀.from _
  first := SSet.stdSimplex.obj₀Equiv.injective (Fin.ext (by omega))
  last := SSet.stdSimplex.obj₀Equiv.injective (Fin.ext (by omega))

private def collapse (S : NecklaceCode) (n : ℕ) : wedge S (chain n) ⟶ S :=
  wedgeMap (𝟙 S) (chainToPoint n) ≫ wedgeRightUnitCode S

private theorem card_le (S : NecklaceCode) (n : ℕ) :
    n + 1 ≤ (wedge S (chain n)).joints.card := by
  calc
    n + 1 = (chain n).joints.card := by simp [chain]
    _ = ((chain n).joints.image (wedgeRight S (chain n))).card :=
      (Finset.card_image_of_injective _ (wedgeRight S (chain n)).injective).symm
    _ ≤ (wedge S (chain n)).joints.card := Finset.card_le_card Finset.subset_union_right

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
local notation "C" => CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y) Q

/-- Every original comma object has graph predecessors with arbitrarily many
joint vertices in their decorated codes. The added beads collapse at the last endpoint. -/
theorem exists_large (U : C) (n : ℕ) :
    ∃ V : C, Nonempty (V ⟶ U) ∧ n < (code V.left).joints.card := by
  obtain ⟨E, _⟩ := JTGraphMultiBeadIdentityLift.exists_identity_lift U.left
  let S := U.left.fiber.left
  let D := JTGraphLiftRestriction.restrict E (collapse S n)
  refine ⟨JTGraphRestrictionRaw.predecessor D, ⟨JTGraphTransportNaturality.toComma D⟩, ?_⟩
  change n < (wedge S (chain n)).joints.card
  exact card_le S n

end
end DaggerModels.PartII.JTGraphLargePredecessor
