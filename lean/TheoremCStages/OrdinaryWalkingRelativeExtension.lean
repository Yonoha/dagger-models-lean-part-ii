import OrdinaryWalkingAlternatingPushout
import RelativeSelectedLeftOuterHornFilling

/-!
# Relative extension across one alternating walking-groupoid stage

The actual stage pushout converts a relative extension into the selected
left outer-horn problem. An invertible first edge supplies the required
outer-horn filler, and the pushout glues it to the old stage map. The
extension retains the prescribed base simplex on the whole new stage.
No general outer-horn lifting-property premise is used here.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial
open DaggerOriginalInnerHornFillers
open DaggerOriginalOrdinaryKanCoreEdgeMembership
open DaggerModels.PartII.RelativeLeftOuterHornGeometry

namespace DaggerModels.PartII.OrdinaryWalkingRelativeExtension

open OrdinaryWalkingAlternatingFiltration
open OrdinaryWalkingAlternatingAttachment
open OrdinaryWalkingAlternatingPushout
open RelativeSelectedLeftOuterHornFilling

noncomputable section

/-- The literal inclusion of the old alternating stage in the new one. -/
def stageInclusion (k : ℕ) :
    (stage (k + 1) : SSet) ⟶ (stage (k + 2) : SSet) :=
  SSet.Subcomplex.homOfLE (stage_le_succ (k + 1))

/-- A relative lift over one actual alternating attachment. The only
non-inner-horn condition is invertibility of the specified first edge of
the attaching horn, measured in the original source `C`. -/
theorem extend_one_stage {C D : SSet} (p : C ⟶ D)
    (hp : DaggerNativeInnerHornFactorization.innerFibrations p)
    (hC : innerHornFillers C) (hD : innerHornFillers D)
    (k : ℕ) (f : (stage (k + 1) : SSet) ⟶ C)
    (β : (stage (k + 2) : SSet) ⟶ D)
    (w : f ≫ p = stageInclusion k ≫ β)
    (he : edgeIsInvertible C
      (SSet.yonedaEquiv (firstEdgeInclusion k ≫ (hornToPrevious k ≫ f)))) :
    ∃ g : (stage (k + 2) : SSet) ⟶ C,
      stageInclusion k ≫ g = f ∧ g ≫ p = β := by
  let φ : (SSet.horn (k + 2) (0 : Fin (k + 3)) : SSet) ⟶ C :=
    hornToPrevious k ≫ f
  let γ : (Δ[k + 2] : SSet) ⟶ D :=
    stageAttachmentLift (k + 2) ≫ β
  have hpush := stage_attachment_horn_isPushout k
  have hbase : φ ≫ p =
      (SSet.horn (k + 2) (0 : Fin (k + 3))).ι ≫ γ := by
    dsimp only [φ, γ]
    calc
      (hornToPrevious k ≫ f) ≫ p =
          hornToPrevious k ≫ (f ≫ p) := Category.assoc _ _ _
      _ = hornToPrevious k ≫ (stageInclusion k ≫ β) := by rw [w]
      _ = (hornToPrevious k ≫ stageInclusion k) ≫ β :=
        (Category.assoc _ _ _).symm
      _ = ((SSet.horn (k + 2) (0 : Fin (k + 3))).ι ≫
            stageAttachmentLift (k + 2)) ≫ β := by
        exact congrArg (fun t ↦ t ≫ β) hpush.w
      _ = (SSet.horn (k + 2) (0 : Fin (k + 3))).ι ≫
          (stageAttachmentLift (k + 2) ≫ β) := Category.assoc _ _ _
  obtain ⟨σ, hσ, hσbase⟩ :=
    selected_left_outer_horn_filler_over p hp hC hD k φ γ hbase he
  let g : (stage (k + 2) : SSet) ⟶ C :=
    hpush.desc f σ hσ
  refine ⟨g, ?_, ?_⟩
  · exact hpush.inl_desc f σ hσ
  · apply hpush.hom_ext
    · calc
        stageInclusion k ≫ (g ≫ p) =
            (stageInclusion k ≫ g) ≫ p := (Category.assoc _ _ _).symm
        _ = f ≫ p := congrArg (fun t ↦ t ≫ p) (hpush.inl_desc f σ hσ)
        _ = stageInclusion k ≫ β := w
    · calc
        stageAttachmentLift (k + 2) ≫ (g ≫ p) =
            (stageAttachmentLift (k + 2) ≫ g) ≫ p :=
          (Category.assoc _ _ _).symm
        _ = σ ≫ p := by rw [hpush.inr_desc]
        _ = stageAttachmentLift (k + 2) ≫ β := hσbase

#print axioms stageInclusion
#print axioms extend_one_stage

end

end DaggerModels.PartII.OrdinaryWalkingRelativeExtension
