import DaggerModelsPartII.JTGraphSingleBeadLiftUniqueness

/-!
# Restricting actual graph lifts along original native necklace morphisms
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphLiftRestriction

open JTProjectiveOrderedFiberComparison JTGraphLiftTransport JTNecklaceEndpointCylinder
open JTCommaGraphPredecessor (augmentationCode)
open NecklaceCode

noncomputable section

variable {W : SegalLocalizers.ReverseDaggerSpace.{0}} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {P : Pres (W := W) (x := x) (y := y)} {R S T : NecklaceCode}

/-- Precomposition retains the entire traversal in the original cylinder. -/
def restrict (E : GraphLift P T) (g : S ⟶ T) : GraphLift P S where
  collapse := g ≫ E.collapse
  parameter := g.map ≫ E.parameter
  comm := by
    have h : ((g ≫ E.collapse) ≫ augmentationCode P).map =
        g.map ≫ (E.collapse ≫ augmentationCode P).map := by
      exact congrArg (fun k : S ⟶ code P ↦ k.map) (Category.assoc _ _ _)
    rw [h]
    rw [← CartesianMonoidalCategory.comp_lift, Category.assoc, E.comm, ← Category.assoc]
    rfl

/-- Identity native restriction preserves the lift. -/
theorem restrict_id (E : GraphLift P T) : restrict E (𝟙 T) = E := by
  apply GraphLift.ext
  · exact Category.id_comp _
  · exact Category.id_comp _

/-- Two successive restrictions are restriction along the composite. -/
theorem restrict_comp (E : GraphLift P T) (f : R ⟶ S) (g : S ⟶ T) :
    restrict (restrict E g) f = restrict E (f ≫ g) := by
  apply GraphLift.ext
  · exact (Category.assoc _ _ _).symm
  · exact (Category.assoc _ _ _).symm

/-- The parameter of a prescribed one-bead lift is the restriction of any
identity-collapse lift, for a label code with distinct endpoints. -/
theorem parameter_eq_restrict_identity {d : ℕ}
    (D : GraphLift P (single d)) (E : GraphLift P P.fiber.left)
    (hE : E.collapse = 𝟙 _) (ht : NecklaceCode.first.{0} (code P) ≠ NecklaceCode.last.{0} (code P)) :
    D.parameter = D.collapse.map ≫ E.parameter := by
  refine JTGraphSingleBeadLiftUniqueness.parameter_eq_of_same_collapse
    D (restrict E D.collapse) ?_ ht
  change D.collapse = D.collapse ≫ E.collapse
  rw [hE, Category.comp_id]

end

end DaggerModels.PartII.JTGraphLiftRestriction
