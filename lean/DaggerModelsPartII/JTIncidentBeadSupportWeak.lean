import DaggerModelsPartII.JTIncidentBeadCombinatorics
import DaggerModelsPartII.JTIncidentBeadSupportData
import DaggerModelsPartII.JTTwoFaceUnionWeak

/-! Weakness of the actual union of full timed faces incident to the selected gap vertex. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Simplicial HomotopicalAlgebra
open DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTIncidentBeadSupportWeak

open JTIncidentBeadSupportData

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (Opposite.op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory}
variable (F : JTParametrizedTargetFamilies.Family Q L time) (j : JTTargetJointMarks.Joint Q.code)
variable (p : Index F j)

/-- With no incident positive bead, the actual support is its retained vertex face. -/
theorem support_eq_vertex_of_no_incident
    (h : ∀ B : (gap F j p).Bead, ¬ Incident F j p B) :
    support F j p = vertexFace F j p := by
  apply le_antisymm _ (vertexFace_le_support F j p)
  apply sup_le le_rfl
  apply iSup_le
  intro B
  exact False.elim (h B.val B.property)

/-- A unique incident bead absorbs the entire retained vertex face. -/
theorem support_eq_bead_of_unique (B₀ : (gap F j p).Bead)
    (h₀ : Incident F j p B₀)
    (h : ∀ B, Incident F j p B → B = B₀) : support F j p = beadFace F j p B₀ := by
  apply le_antisymm _ (beadFace_le_support F j p B₀ h₀)
  apply sup_le (vertexFace_le_beadFace F j p B₀ h₀)
  apply iSup_le
  intro B
  rw [h B.val B.property]

/-- Two incident beads covering all incident beads give their literal two-face union. -/
theorem support_eq_two_beads_of_cover (B₀ B₁ : (gap F j p).Bead)
    (h₀ : Incident F j p B₀) (h₁ : Incident F j p B₁)
    (h : ∀ B, Incident F j p B → B = B₀ ∨ B = B₁) :
    support F j p = beadFace F j p B₀ ⊔ beadFace F j p B₁ := by
  apply le_antisymm
  · apply sup_le
    · exact (vertexFace_le_beadFace F j p B₀ h₀).trans le_sup_left
    · apply iSup_le
      intro B
      rcases h B.val B.property with hB | hB
      · rw [hB]
        exact le_sup_left
      · rw [hB]
        exact le_sup_right
  · exact sup_le (beadFace_le_support F j p B₀ h₀) (beadFace_le_support F j p B₁ h₁)

private theorem face_weak {m : ℕ} (S : Finset (Fin (m + 1))) (v : Fin (m + 1))
    (hv : v ∈ S) :
    WeakEquivalence ((SSet.stdSimplex.face S : (Δ[m] : SSet.{0}).Subcomplex).ι) := by
  have h := JTTwoFaceUnionWeak.union_weak_of_common_vertex S S v hv hv
  change WeakEquivalence (((SSet.stdSimplex.face S : (Δ[m] : SSet.{0}).Subcomplex) ⊔
    SSet.stdSimplex.face S).ι) at h
  rw [sup_idem] at h
  exact h

/-- The actual support inclusion is a monomorphism, without a weakness hypothesis. -/
theorem support_mono : Mono (support F j p).ι := by infer_instance

/-- The actual full incident-face union includes weakly into the original coefficient simplex. -/
theorem support_weak : WeakEquivalence (support F j p).ι := by
  obtain ⟨v, hv⟩ := vertexSet_nonempty F j p
  rcases JTIncidentBeadCombinatorics.incident_cases (gap F j p) (gapCoordinate F j p) with
    h | ⟨B₀, h₀, h⟩ | ⟨B₀, B₁, _, h₀, h₁, h⟩
  · rw [support_eq_vertex_of_no_incident F j p h, vertexFace_eq_face]
    exact face_weak (vertexSet F j p) v hv
  · rw [support_eq_bead_of_unique F j p B₀ h₀ h, beadFace_eq_face]
    exact face_weak (beadSet F j p B₀) v (vertexSet_subset_beadSet F j p B₀ h₀ hv)
  · rw [support_eq_two_beads_of_cover F j p B₀ B₁ h₀ h₁ h,
      beadFace_eq_face, beadFace_eq_face]
    exact JTTwoFaceUnionWeak.union_weak_of_common_vertex
      (beadSet F j p B₀) (beadSet F j p B₁) v
      (vertexSet_subset_beadSet F j p B₀ h₀ hv)
      (vertexSet_subset_beadSet F j p B₁ h₁ hv)

end
end DaggerModels.PartII.JTIncidentBeadSupportWeak
