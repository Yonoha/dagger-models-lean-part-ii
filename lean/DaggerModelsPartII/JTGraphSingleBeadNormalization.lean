import DaggerModelsPartII.JTGraphLiftRestriction
import DaggerModelsPartII.JTGraphIdentityLift

/-!
# Simultaneous normalization of one-bead lifts over a fixed original traversal
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphSingleBeadNormalization

open JTProjectiveOrderedFiberComparison JTGraphLiftTransport JTGraphLiftRestriction

noncomputable section

variable {W : SegalLocalizers.ReverseDaggerSpace.{0}} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {P : Pres (W := W) (x := x) (y := y)}

/-- The prescribed graph lift is literally the restriction along its own collapse. -/
theorem eq_restrict_identity {d : ℕ}
    (D : GraphLift P (NecklaceCode.single d)) (E : GraphLift P P.fiber.left)
    (hE : E.collapse = 𝟙 _)
    (ht : NecklaceCode.first.{0} (code P) ≠ NecklaceCode.last.{0} (code P)) :
    D = restrict E D.collapse := by
  apply GraphLift.ext
  · change D.collapse = D.collapse ≫ E.collapse
    rw [hE, Category.comp_id]
  · exact parameter_eq_restrict_identity D E hE ht

/-- All one-bead lifts, allowing different bead degrees and collapse maps,
are restrictions of the same identity-collapse lift. -/
theorem exists_identity_normalization {d : ℕ}
    (hP : P.fiber.left = NecklaceCode.single d)
    (ht : NecklaceCode.first.{0} (code P) ≠ NecklaceCode.last.{0} (code P)) :
    ∃ E : GraphLift P P.fiber.left, E.collapse = 𝟙 _ ∧
      ∀ (e : ℕ) (D : GraphLift P (NecklaceCode.single e)), D = restrict E D.collapse := by
  obtain ⟨E, hE⟩ := JTGraphIdentityLift.exists_identity_lift hP
  exact ⟨E, hE, fun _ D ↦ eq_restrict_identity D E hE ht⟩

end

end DaggerModels.PartII.JTGraphSingleBeadNormalization
