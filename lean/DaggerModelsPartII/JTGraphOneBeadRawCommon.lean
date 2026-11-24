import DaggerModelsPartII.JTGraphTransportRaw
import DaggerModelsPartII.JTGraphPointTransport
import DaggerModelsPartII.JTGraphSingleBeadNormalization

/-!
# A common actual graph comparison for a fixed one-bead internal necklace
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphOneBeadRawCommon

open JTProjectiveOrderedFiberComparison JTGraphLiftTransport JTGraphLiftRestriction
open JTGraphRestrictionRaw

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}

private abbrev TargetComma (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)) :=
  CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y) Q

private theorem eq_restrict_at_zero {P : Pres (W := W) (x := x) (y := y)}
    {S : NecklaceCode} (hd : degree P = ⦋0⦌)
    (D : GraphLift P S) (E : GraphLift P P.fiber.left) (hE : E.collapse = 𝟙 _) :
    D = restrict E D.collapse := by
  have ht : IsTerminal (J.obj (degree P)) := by
    rw [hd]
    exact JTParameterZero.parameterZeroIsTerminal
  apply GraphLift.ext
  · change D.collapse = D.collapse ≫ E.collapse
    rw [hE, Category.comp_id]
  · exact ht.hom_ext _ _

/-- All prescribed one-bead lifts over an original one-bead internal
necklace have arrows to a common graph in the original fixed-target comma.
At a point label the original presentation can first move to degree zero. -/
theorem exists_common_raw (U : TargetComma Q) {d : ℕ}
    (hU : U.left.fiber.left = NecklaceCode.single d) :
    ∃ (V : TargetComma Q) (_ : U ⟶ V) (E : GraphLift V.left V.left.fiber.left),
      V.left.fiber.left = U.left.fiber.left ∧ E.collapse = 𝟙 _ ∧
      ∀ (e : ℕ) (D : GraphLift U.left (NecklaceCode.single e)),
        Nonempty (predecessor D ⟶ predecessor E) := by
  classical
  by_cases ht : NecklaceCode.first.{0} (code U.left) = NecklaceCode.last.{0} (code U.left)
  · obtain ⟨V, a, hd, _, hv, _⟩ := JTGraphPointTransport.exists_zero_transport U ht
    obtain ⟨E, hE⟩ := JTGraphIdentityLift.exists_identity_lift (hv.trans hU)
    refine ⟨V, a, E, hv, hE, ?_⟩
    intro e D
    let D' := D.transport a.left
    have hD := eq_restrict_at_zero hd D' E hE
    exact ⟨JTGraphTransportRaw.commaTransport D a ≫
      eqToHom (congrArg (fun G ↦ predecessor G) hD) ≫ commaRestriction E D'.collapse⟩
  · obtain ⟨E, hE, hnorm⟩ := JTGraphSingleBeadNormalization.exists_identity_normalization hU ht
    refine ⟨U, 𝟙 U, E, rfl, hE, ?_⟩
    intro e D
    exact ⟨eqToHom (congrArg (fun G ↦ predecessor G) (hnorm e D)) ≫
      commaRestriction E D.collapse⟩

end

end DaggerModels.PartII.JTGraphOneBeadRawCommon
