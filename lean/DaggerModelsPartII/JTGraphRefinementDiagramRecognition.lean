import DaggerModelsPartII.JTGraphRefinementMixedArrow

/-!
# A diagram of actual comma arrows lifts to strict graph refinements

It suffices to recover each actual arrow between the specified representatives.
Faithfulness supplies strict identity and composition of the recovered arrows.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphRefinementDiagramRecognition

open JTGraphRefinement JTGraphRefinementMixedArrow
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}

private abbrev Target :=
  CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y) Q

variable {I : Type} [SmallCategory I]
variable (U : I ⥤ Target (Q := Q))
variable (D : I → Refinement W x y Q)
variable (e : ∀ i, U.obj i ≅ (D i).toComma)

/-- Rewrite the objects of the actual diagram to their specified representatives. -/
abbrev represented : I ⥤ Target (Q := Q) := U.copyObj (fun i ↦ (D i).toComma) e

/-- The only morphism obligation is that each conjugated actual arrow lifts. -/
def ArrowsLift : Prop :=
  ∀ ⦃i j : I⦄ (a : i ⟶ j), ∃ b : D i ⟶ D j,
    (evaluate Q).map b = (represented U D e).map a

variable (h : ArrowsLift U D e)

private def arrow {i j : I} (a : i ⟶ j) : D i ⟶ D j := (h a).choose

private theorem arrow_evaluation {i j : I} (a : i ⟶ j) :
    (evaluate Q).map (arrow U D e h a) = (represented U D e).map a :=
  (h a).choose_spec

/-- The recovered strict diagram has the same maps after evaluation. -/
def lifted : I ⥤ Refinement W x y Q where
  obj := D
  map := arrow U D e h
  map_id i := by
    apply (evaluate Q).map_injective
    rw [arrow_evaluation, (represented U D e).map_id, (evaluate Q).map_id]
    rfl
  map_comp a b := by
    apply (evaluate Q).map_injective
    rw [arrow_evaluation, (represented U D e).map_comp, (evaluate Q).map_comp,
      arrow_evaluation, arrow_evaluation]

/-- Evaluating the strict lift recovers the actual diagram on the nose at
the prescribed object representatives. -/
theorem lifted_evaluate : lifted U D e h ⋙ evaluate Q = represented U D e := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro i j a
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact arrow_evaluation U D e h a

/-- The exact comparison to the actual fixed-target diagram on its original objects. -/
def comparison : U ≅ lifted U D e h ⋙ evaluate Q :=
  U.isoCopyObj (fun i ↦ (D i).toComma) e ≪≫ eqToIso (lifted_evaluate U D e h).symm

end

end DaggerModels.PartII.JTGraphRefinementDiagramRecognition
