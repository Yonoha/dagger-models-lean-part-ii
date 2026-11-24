import DaggerModelsPartII.JTTwoFaceUnionWeak

/-! Exact inverse images of two genuine simplex faces under an ordinal surjection. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTOrdinalTwoFaceUnionPullback

noncomputable section

variable {k m : ℕ} (α : ⦋k⦌ ⟶ ⦋m⦌)

/-- All actual source vertices whose original image lies in the specified old face. -/
def inverseVertices (S : Finset (Fin (m + 1))) : Finset (Fin (k + 1)) :=
  Finset.univ.filter (fun w ↦ α.toOrderHom w ∈ S)

@[simp] theorem mem_inverseVertices (S : Finset (Fin (m + 1))) (w : Fin (k + 1)) :
    w ∈ inverseVertices α S ↔ α.toOrderHom w ∈ S := by
  simp only [inverseVertices, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The full subcomplex preimage of one face is its actual inverse-vertex face. -/
theorem face_preimage (S : Finset (Fin (m + 1))) :
    (SSet.stdSimplex.face S : (Δ[m] : SSet.{0}).Subcomplex).preimage
        (SSet.stdSimplex.map α) = SSet.stdSimplex.face (inverseVertices α S) := by
  ext q x
  induction q using Opposite.rec with | op q =>
    induction q using SimplexCategory.rec with | _ n =>
      change (SSet.stdSimplex.map α).app (op ⦋n⦌) x ∈
        (SSet.stdSimplex.face S).obj (op ⦋n⦌) ↔
          x ∈ (SSet.stdSimplex.face (inverseVertices α S)).obj (op ⦋n⦌)
      rw [SSet.stdSimplex.mem_face_iff, SSet.stdSimplex.mem_face_iff]
      simp only [mem_inverseVertices]
      rfl

/-- Pullback preserves the genuine union of the two faces, without taking a vertex hull. -/
theorem union_preimage (S T : Finset (Fin (m + 1))) :
    ((SSet.stdSimplex.face S : (Δ[m] : SSet.{0}).Subcomplex) ⊔
        SSet.stdSimplex.face T).preimage (SSet.stdSimplex.map α) =
      SSet.stdSimplex.face (inverseVertices α S) ⊔
        SSet.stdSimplex.face (inverseVertices α T) := by
  rw [SSet.Subcomplex.preimage_max, face_preimage, face_preimage]

/-- A common old vertex has a common actual source lift under the ordinal surjection. -/
theorem common_source_vertex (hα : Function.Surjective α.toOrderHom)
    (S T : Finset (Fin (m + 1))) (v : Fin (m + 1)) (hvS : v ∈ S) (hvT : v ∈ T) :
    ∃ w : Fin (k + 1), α.toOrderHom w = v ∧
      w ∈ inverseVertices α S ∧ w ∈ inverseVertices α T := by
  obtain ⟨w, hw⟩ := hα v
  refine ⟨w, hw, (mem_inverseVertices α S w).mpr ?_,
    (mem_inverseVertices α T w).mpr ?_⟩
  · exact hw ▸ hvS
  · exact hw ▸ hvT

/-- The actual inverse-image union inclusion is always mono. -/
theorem preimage_union_mono (S T : Finset (Fin (m + 1))) :
    Mono (((SSet.stdSimplex.face S : (Δ[m] : SSet.{0}).Subcomplex) ⊔
      SSet.stdSimplex.face T).preimage (SSet.stdSimplex.map α)).ι := by
  infer_instance

/-- A surjective ordinal pullback of these two common-vertex faces has Kan weak inclusion. -/
theorem preimage_union_weak (hα : Function.Surjective α.toOrderHom)
    (S T : Finset (Fin (m + 1))) (v : Fin (m + 1)) (hvS : v ∈ S) (hvT : v ∈ T) :
    WeakEquivalence (((SSet.stdSimplex.face S : (Δ[m] : SSet.{0}).Subcomplex) ⊔
      SSet.stdSimplex.face T).preimage (SSet.stdSimplex.map α)).ι := by
  rw [union_preimage]
  obtain ⟨w, _, hwS, hwT⟩ := common_source_vertex α hα S T v hvS hvT
  exact JTTwoFaceUnionWeak.union_weak_of_common_vertex
    (inverseVertices α S) (inverseVertices α T) w hwS hwT

/-- The one-face case is the same two-face argument with the two old faces equal. -/
theorem preimage_face_weak (hα : Function.Surjective α.toOrderHom)
    (S : Finset (Fin (m + 1))) (v : Fin (m + 1)) (hv : v ∈ S) :
    WeakEquivalence ((SSet.stdSimplex.face S : (Δ[m] : SSet.{0}).Subcomplex).preimage
      (SSet.stdSimplex.map α)).ι := by
  have h := preimage_union_weak α hα S S v hv hv
  rw [sup_idem] at h
  exact h

end
end DaggerModels.PartII.JTOrdinalTwoFaceUnionPullback
