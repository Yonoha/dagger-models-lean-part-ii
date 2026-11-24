import OrdinaryWalkingAlternatingOffHornInjective
import SubcomplexAttachmentWithoutMono

/-!
# The literal alternating outer-horn attachment pushout

Each new stage of the original walking parameter is obtained by attaching
its chosen alternating simplex along the missing-zero outer horn. The
simplex map need not be mono: its repeated simplices already lie in the
previous stage, and it is injective outside that exact intersection.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII.OrdinaryWalkingAlternatingPushout

open OrdinaryWalkingAlternatingFiltration
open OrdinaryWalkingAlternatingAttachment
open OrdinaryWalkingAlternatingIntersection
open OrdinaryWalkingAlternatingOffHornInjective

noncomputable section

private abbrev Walking := GroupoidSimplex.parameter.obj ⦋1⦌

/-- The image of the actual alternating simplex is exactly its generated
stage, even though the simplex map is not globally mono. -/
theorem range_attachmentMap (n : ℕ) :
    SSet.Subcomplex.range (attachmentMap n) = stage n := by
  rw [SSet.Subcomplex.range_eq_ofSimplex]
  rfl

/-- The actual simplex map regarded as a morphism into its new stage. -/
def stageAttachmentLift (n : ℕ) : Δ[n] ⟶ (stage n : SSet) :=
  SSet.Subcomplex.lift (attachmentMap n) (by rw [range_attachmentMap])

/-- The degreewise pushout before replacing its exact preimage by the
identified horn. -/
theorem stage_attachment_preimage_isPushout (k : ℕ) :
    IsPushout
      ((stage (k + 1)).fromPreimage (attachmentMap (k + 2)))
      ((stage (k + 1)).preimage (attachmentMap (k + 2))).ι
      (SSet.Subcomplex.homOfLE (stage_le_succ (k + 1)))
      (stageAttachmentLift (k + 2)) := by
  have hb : SSet.Subcomplex.range (attachmentMap (k + 2)) ≤
      stage (k + 2) := by
    rw [range_attachmentMap]
  have hcover : stage (k + 1) ⊔
      SSet.Subcomplex.range (attachmentMap (k + 2)) =
      stage (k + 2) := by
    rw [range_attachmentMap]
    exact sup_eq_right.mpr (stage_le_succ (k + 1))
  have hinject : ∀ (q : SimplexCategoryᵒᵖ)
      (x y : (Δ[k + 2] : SSet).obj q),
      x ∉ ((stage (k + 1)).preimage (attachmentMap (k + 2))).obj q →
      y ∉ ((stage (k + 1)).preimage (attachmentMap (k + 2))).obj q →
      (attachmentMap (k + 2)).app q x =
        (attachmentMap (k + 2)).app q y → x = y := by
    intro q x y hx hy hxy
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, q = op ⦋m⦌ :=
      ⟨q.unop.len, by simp only [SimplexCategory.mk_len, op_unop]⟩
    rw [preimage_eq_horn] at hx hy
    exact attachmentMap_injective_off_horn k m x y hx hy hxy
  have h := SubcomplexAttachmentWithoutMono.attachment_isPushout
    (stage (k + 1)) (stage (k + 2)) (attachmentMap (k + 2))
    (stage_le_succ (k + 1)) hb hcover hinject
  simpa only [stageAttachmentLift] using h

/-- The literal zero outer horn maps into the preceding literal stage. -/
def hornToPrevious (k : ℕ) :
    (SSet.horn (k + 2) (0 : Fin (k + 3)) : SSet) ⟶
      (stage (k + 1) : SSet) :=
  eqToHom (congrArg
    (fun A : (Δ[k + 2] : SSet).Subcomplex ↦ (A : SSet))
    (preimage_eq_horn k).symm) ≫
    (stage (k + 1)).fromPreimage (attachmentMap (k + 2))

private theorem transport_preimage_pushout {X K D : SSet}
    (H : X.Subcomplex) (b : K ⟶ X) (A : K.Subcomplex)
    (hA : H.preimage b = A) (j : (H : SSet) ⟶ D) (g : K ⟶ D)
    (hpush : IsPushout (H.fromPreimage b) (H.preimage b).ι j g) :
    IsPushout
      (eqToHom (congrArg (fun B : K.Subcomplex ↦ (B : SSet)) hA.symm) ≫
        H.fromPreimage b) A.ι j g := by
  cases hA
  simpa only [eqToHom_refl, Category.id_comp] using hpush

/-- Rezk's actual alternating filtration attaches `Δ[k+2]` along
`Λ[k+2,0]` for every `k`, with both stages inside the original walking
parameter and no monomorphism assumption on the simplex map. -/
theorem stage_attachment_horn_isPushout (k : ℕ) :
    IsPushout (hornToPrevious k)
      (SSet.horn (k + 2) (0 : Fin (k + 3))).ι
      (SSet.Subcomplex.homOfLE (stage_le_succ (k + 1)))
      (stageAttachmentLift (k + 2)) := by
  exact transport_preimage_pushout (stage (k + 1))
    (attachmentMap (k + 2))
    (SSet.horn (k + 2) (0 : Fin (k + 3))) (preimage_eq_horn k)
    (SSet.Subcomplex.homOfLE (stage_le_succ (k + 1)))
    (stageAttachmentLift (k + 2)) (stage_attachment_preimage_isPushout k)

#print axioms range_attachmentMap
#print axioms stage_attachment_preimage_isPushout
#print axioms stage_attachment_horn_isPushout

end

end DaggerModels.PartII.OrdinaryWalkingAlternatingPushout
