import DaggerModelsPartII.JTNativeEndpointPadding
import DaggerModelsPartII.JTGraphFactoredPresentation

/-! Adding beads only to an internal source does not change the decorated joint constraint. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTEndpointPaddingJointObstruction

noncomputable section

/-- The two outer edges add an interior joint even when the middle is a point. -/
theorem padded_joints_card (T : NecklaceCode) :
    3 ≤ (JTNativeEndpointPadding.pad.obj T).joints.card := by
  let P := JTNativeEndpointPadding.pad.obj T
  let i : Fin (P.len + 1) := wedgeLeft (single 1) (wedge T (single 1)) (Fin.last 1)
  let j : Fin (P.len + 1) := Fin.last P.len
  have hi : i ∈ P.joints := by
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, (single 1).last_mem, rfl⟩)
  have h0i : (0 : Fin (P.len + 1)) ≠ i := by
    intro h
    have hh := congrArg Fin.val h
    change (0 : ℕ) = 1 at hh
    omega
  have hij : i ≠ j := by
    intro h
    have hh := congrArg Fin.val h
    change (1 : ℕ) = 1 + (T.len + 1) at hh
    omega
  have h0j : (0 : Fin (P.len + 1)) ≠ j := by
    intro h
    have hh := congrArg Fin.val h
    change (0 : ℕ) = 1 + (T.len + 1) at hh
    omega
  let s : Finset (Fin (P.len + 1)) := {0, i, j}
  have hs : s ⊆ P.joints := by
    intro z hz
    change z ∈ insert 0 (insert i ({j} : Finset (Fin (P.len + 1)))) at hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact P.first_mem
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hi
    have h : z = j := Finset.mem_singleton.mp (show z ∈ ({j} : Finset _) from hz)
    exact h.symm ▸ P.last_mem
  have hc : s.card = 3 := by
    simp [s, Finset.card_insert_of_notMem, h0i, h0j, hij]
  exact hc ▸ Finset.card_le_card hs

/-- A single bead cannot map to a necklace with both extra endpoint beads. -/
theorem no_single_to_padded (d : ℕ) (T : NecklaceCode) :
    IsEmpty (single d ⟶ JTNativeEndpointPadding.pad.obj T) := by
  refine ⟨fun f ↦ ?_⟩
  have hcard : (JTNativeEndpointPadding.pad.obj T).joints.card ≤ (single d).joints.card :=
    (Finset.card_le_card (joints_subset_image f)).trans Finset.card_image_le
  have hs : (single d).joints.card ≤ 2 := by
    change ({(0 : Fin (d + 1)), Fin.last d} : Finset _).card ≤ 2
    exact Finset.card_le_two
  exact (by decide : ¬ 3 ≤ 2) ((padded_joints_card T).trans (hcard.trans hs))

open OrderedNecklaceVertexPoints (boundaryPoint)
open JTProjectiveOrderedFiberComparison (row)

variable {W : SegalLocalizers.ReverseDaggerSpace.{0}}
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {L R : DecoratedNecklaceHomDiagram.Index W x y}

/-- Keeping the old one-bead decorated code prevents a forward label map into the padded target. -/
theorem no_label_arrow (d : ℕ) (T : NecklaceCode)
    (hL : OrderedLabelElements.necklace W (boundaryPoint W x y) L = single d)
    (hR : OrderedLabelElements.necklace W (boundaryPoint W x y) R =
      JTNativeEndpointPadding.pad.obj T) : IsEmpty (L ⟶ R) := by
  refine ⟨fun f ↦ ?_⟩
  have g : OrderedLabelElements.necklace W (boundaryPoint W x y) L ⟶
      OrderedLabelElements.necklace W (boundaryPoint W x y) R :=
    ((OrderedLabelElements.projection W (boundaryPoint W x y)).map f).1
  exact (no_single_to_padded d T).false (hL ▸ hR ▸ g)

private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev Raw :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)

variable {Q : NecklacesOver (Raw (W := W)) (rawVertex W x) (rawVertex W y)}
variable {U V : JTGraphFactoredPresentation.TargetComma Q}

/-- The joint obstruction also excludes a direct arrow in the actual fixed-target comma. -/
theorem no_comma_arrow (d : ℕ) (T : NecklaceCode)
    (hU : OrderedLabelElements.necklace W (boundaryPoint W x y) U.left.base = single d)
    (hV : OrderedLabelElements.necklace W (boundaryPoint W x y) V.left.base =
      JTNativeEndpointPadding.pad.obj T) : IsEmpty (U ⟶ V) :=
  ⟨fun f ↦ (no_label_arrow d T hU hV).false f.left.base⟩

end

end DaggerModels.PartII.JTEndpointPaddingJointObstruction
