import DaggerModelsPartII.JTFiniteCoefficientBridgeSubcollection
import DaggerModelsPartII.JTInterleavedTimeFace

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open MonoidalCategory CartesianMonoidalCategory
open scoped SSet.modelCategoryQuillen

universe v

namespace DaggerModels.PartII.JTFiniteCoefficientBridgeCopyFace

open JTFiniteCoefficientBridgeOrder (bridge vertexEquiv)
open JTFiniteCoefficientBridgeTime (time timeVertexEquiv)
open JTFiniteCoefficientBridgePrism (prism rankVertex rankVertex_apply)
open JTFiniteCoefficientBridgeSubcollection
open SSet.Subcomplex

noncomputable section

private abbrev simplex (a : SimplexCategory) := SSet.stdSimplex.{v}.obj a

variable {m : ℕ} {k b' : SimplexCategory}
variable {b : Fin (m + 1) → SimplexCategory}
variable (c : ∀ e, k ⟶ b e) (u : k ⟶ b') (n : SimplexCategory)

private def copyVertices (S : Finset (Fin (m + 1))) :
    Finset (Fin ((bridge k n m).len + 1)) :=
  Finset.univ.filter (fun z ↦ ((vertexEquiv c u n).symm z).2 ∈ S)

private def timeVertices (S : Finset (Fin (m + 1))) :
    Finset (Fin ((time m n).len + 1)) :=
  Finset.univ.filter (fun z ↦ ((timeVertexEquiv m n).symm z).1 ∈ S)

abbrev copyFace (S : Finset (Fin (m + 1))) : (simplex.{v} (bridge k n m)).Subcomplex :=
  SSet.stdSimplex.face (copyVertices c u n S)

abbrev timeFace (S : Finset (Fin (m + 1))) : (simplex.{v} (time m n)).Subcomplex :=
  SSet.stdSimplex.face (timeVertices n S)

@[simp] theorem mem_copyVertices (S : Finset (Fin (m + 1)))
    (z : Fin ((bridge k n m).len + 1)) :
    z ∈ copyVertices c u n S ↔ ((vertexEquiv c u n).symm z).2 ∈ S := by
  simp [copyVertices]

@[simp] theorem mem_timeVertices (S : Finset (Fin (m + 1)))
    (z : Fin ((time m n).len + 1)) :
    z ∈ timeVertices (m := m) n S ↔ ((timeVertexEquiv m n).symm z).1 ∈ S := by
  simp [timeVertices]

@[simp] theorem mem_copyFace_iff (S : Finset (Fin (m + 1)))
    {d : ℕ} (z : (simplex.{v} (bridge k n m)).obj (op ⦋d⦌)) :
    z ∈ (copyFace c u n S).obj _ ↔
      ∀ a : Fin (d + 1),
        ((vertexEquiv c u n).symm ((SSet.stdSimplex.objEquiv z).toOrderHom a)).2 ∈ S := by
  change z ∈ (SSet.stdSimplex.face (copyVertices c u n S)).obj _ ↔ _
  rw [SSet.stdSimplex.mem_face_iff]
  simp only [mem_copyVertices]
  rfl

@[simp] theorem mem_timeFace_iff (S : Finset (Fin (m + 1)))
    {d : ℕ} (z : (simplex.{v} (time m n)).obj (op ⦋d⦌)) :
    z ∈ (timeFace n S).obj _ ↔
      ∀ a : Fin (d + 1),
        ((timeVertexEquiv m n).symm ((SSet.stdSimplex.objEquiv z).toOrderHom a)).1 ∈ S := by
  change z ∈ (SSet.stdSimplex.face (timeVertices n S)).obj _ ↔ _
  rw [SSet.stdSimplex.mem_face_iff]
  simp only [mem_timeVertices]
  rfl

theorem copyFace_univ : copyFace.{v} c u n Finset.univ = ⊤ := by
  ext q z
  cases q using Opposite.rec with
  | op q =>
    cases q using SimplexCategory.rec with
    | _ d => simp [mem_copyFace_iff]

theorem timeFace_univ : timeFace.{v} (m := m) n Finset.univ = ⊤ := by
  ext q z
  cases q using Opposite.rec with
  | op q =>
    cases q using SimplexCategory.rec with
    | _ d => simp [mem_timeFace_iff]

theorem copyFace_mono {S T : Finset (Fin (m + 1))} (h : S ⊆ T) :
    copyFace.{v} c u n S ≤ copyFace c u n T := by
  intro q z hz
  simp only [copyFace, SSet.stdSimplex.face_obj] at hz ⊢
  intro x hx
  exact (mem_copyVertices c u n T x).2 (h ((mem_copyVertices c u n S x).1 (hz hx)))

theorem timeFace_mono {S T : Finset (Fin (m + 1))} (h : S ⊆ T) :
    timeFace.{v} (m := m) n S ≤ timeFace n T := by
  intro q z hz
  simp only [timeFace, SSet.stdSimplex.face_obj] at hz ⊢
  intro x hx
  exact (mem_timeVertices (m := m) n T x).2
    (h ((mem_timeVertices (m := m) n S x).1 (hz hx)))

theorem copyFace_inter (S T : Finset (Fin (m + 1))) :
    copyFace.{v} c u n (S ∩ T) = copyFace c u n S ⊓ copyFace c u n T := by
  have h : copyVertices c u n (S ∩ T) =
      copyVertices c u n S ∩ copyVertices c u n T := by
    ext z
    simp
  simpa only [copyFace, h] using
    (SSet.stdSimplex.face_inter_face (copyVertices c u n S) (copyVertices c u n T)).symm

theorem timeFace_inter (S T : Finset (Fin (m + 1))) :
    timeFace.{v} (m := m) n (S ∩ T) = timeFace n S ⊓ timeFace n T := by
  have h : timeVertices (m := m) n (S ∩ T) =
      timeVertices n S ∩ timeVertices n T := by
    ext z
    simp
  simpa only [timeFace, h] using
    (SSet.stdSimplex.face_inter_face (timeVertices n S) (timeVertices n T)).symm

theorem copyFace_empty : copyFace.{v} c u n ∅ = ⊥ := by
  ext q z
  cases q using Opposite.rec with
  | op q =>
    cases q using SimplexCategory.rec with
    | _ d =>
      change z ∈ (SSet.stdSimplex.face (copyVertices c u n ∅)).obj _ ↔ False
      rw [SSet.stdSimplex.mem_face_iff]
      simp

theorem timeFace_empty : timeFace.{v} (m := m) n ∅ = ⊥ := by
  ext q z
  cases q using Opposite.rec with
  | op q =>
    cases q using SimplexCategory.rec with
    | _ d =>
      change z ∈ (SSet.stdSimplex.face (timeVertices (m := m) n ∅)).obj _ ↔ False
      rw [SSet.stdSimplex.mem_face_iff]
      simp

theorem copyFace_preimage_prism (S : Finset (Fin (m + 1))) :
    (copyFace.{v} c u n S).preimage (prism c u n) =
      (⊤ : (simplex.{v} k).Subcomplex).prod (timeFace n S) := by
  ext q x
  cases q using Opposite.rec with
  | op q =>
    cases q using SimplexCategory.rec with
    | _ d =>
      change (prism c u n).app _ x ∈ (copyFace c u n S).obj _ ↔
        x.1 ∈ (⊤ : (simplex k).Subcomplex).obj _ ∧
          x.2 ∈ (timeFace n S).obj _
      simp only [copyFace, timeFace, SSet.stdSimplex.face_obj, Finset.le_eq_subset,
        Finset.image_subset_iff,
        Subfunctor.top_obj, Set.top_eq_univ, Set.mem_univ, true_and]
      constructor
      · intro hx a ha
        have h := hx a ha
        have hpr := JTFiniteCoefficientBridgePrism.prism_app.{v} c u n (op ⦋d⦌) x a
        simp only [mem_copyVertices] at h
        simp only [mem_timeVertices]
        have hcopy := congrArg (fun z ↦ ((vertexEquiv c u n).symm z).2) hpr
        have hcopy' : ((vertexEquiv c u n).symm
            ((SSet.stdSimplex.objEquiv ((prism c u n).app _ x)).toOrderHom a)).2 =
            ((timeVertexEquiv m n).symm
              ((SSet.stdSimplex.objEquiv x.2).toOrderHom a)).1 := by
          simpa only [rankVertex, Equiv.symm_apply_apply] using hcopy
        exact hcopy' ▸ h
      · intro hx a ha
        have h := hx a ha
        have hpr := JTFiniteCoefficientBridgePrism.prism_app.{v} c u n (op ⦋d⦌) x a
        simp only [mem_timeVertices] at h
        simp only [mem_copyVertices]
        have hcopy := congrArg (fun z ↦ ((vertexEquiv c u n).symm z).2) hpr
        have hcopy' : ((vertexEquiv c u n).symm
            ((SSet.stdSimplex.objEquiv ((prism c u n).app _ x)).toOrderHom a)).2 =
            ((timeVertexEquiv m n).symm
              ((SSet.stdSimplex.objEquiv x.2).toOrderHom a)).1 := by
          simpa only [rankVertex, Equiv.symm_apply_apply] using hcopy
        exact hcopy'.symm ▸ h

abbrev smallDegree (S : Finset (Fin (m + 1))) : SimplexCategory :=
  JTHigherInterleavedParameter.timeDegree S

abbrev copyInclusion (S : Finset (Fin (m + 1))) (hS : S.Nonempty) :
    smallDegree S ⟶ ⦋m⦌ :=
  JTHigherInterleavedParameter.timeInclusion S hS

abbrev smallCoefficients (S : Finset (Fin (m + 1))) (hS : S.Nonempty) :
    ∀ e : Fin ((smallDegree S).len + 1),
      k ⟶ b ((copyInclusion S hS).toOrderHom e) :=
  fun e ↦ c ((copyInclusion S hS).toOrderHom e)

theorem smallCoefficient_agrees (S : Finset (Fin (m + 1)))
    (hS : S.Nonempty) (e : Fin ((smallDegree S).len + 1))
    (x : Fin (k.len + 1) × Fin (n.len + 1)) :
    JTCommonCoefficientParameter.vertexEquiv (smallCoefficients c S hS e) n x =
      JTCommonCoefficientParameter.vertexEquiv
        (c ((copyInclusion S hS).toOrderHom e)) n x := rfl

abbrev smallOperator (S : Finset (Fin (m + 1))) (hS : S.Nonempty) :
    bridge k n (smallDegree S).len ⟶ bridge k n m :=
  coefficientOperator (smallCoefficients c S hS) c u n (copyInclusion S hS)
    (JTHigherInterleavedParameter.timeInclusion_injective S hS)
    (smallCoefficient_agrees c n S hS)

theorem copyRange_iff (S : Finset (Fin (m + 1))) (hS : S.Nonempty)
    (z : Fin ((bridge k n m).len + 1)) :
    z ∈ Set.range
      (coefficientOperator (smallCoefficients c S hS) c u n
        (copyInclusion S hS)
        (JTHigherInterleavedParameter.timeInclusion_injective S hS)
        (smallCoefficient_agrees c n S hS)).toOrderHom ↔
      ((vertexEquiv c u n).symm z).2 ∈ S := by
  obtain ⟨x, rfl⟩ := (vertexEquiv c u n).surjective z
  rw [Equiv.symm_apply_apply]
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨y, rfl⟩ :=
      (vertexEquiv (smallCoefficients c S hS) u n).surjective w
    rw [coefficientOperator, JTFiniteCoefficientBridgeOrder.mapCopies_vertexEquiv] at hw
    have he := congrArg Prod.snd ((vertexEquiv c u n).injective hw)
    have hy : (copyInclusion S hS).toOrderHom y.2 ∈ S := by
      simpa only [JTHigherInterleavedParameter.timeInclusion_range, Finset.mem_coe]
        using (show (copyInclusion S hS).toOrderHom y.2 ∈
          Set.range (copyInclusion S hS).toOrderHom from ⟨y.2, rfl⟩)
    exact he ▸ hy
  · intro hx
    have hrange : x.2 ∈ Set.range (copyInclusion S hS).toOrderHom := by
      rw [JTHigherInterleavedParameter.timeInclusion_range S hS]
      exact hx
    obtain ⟨e, he⟩ := hrange
    refine ⟨vertexEquiv (smallCoefficients c S hS) u n (x.1, e), ?_⟩
    rw [coefficientOperator, JTFiniteCoefficientBridgeOrder.mapCopies_vertexEquiv]
    change vertexEquiv c u n (x.1, (copyInclusion S hS).toOrderHom e) =
      vertexEquiv c u n (x.1, x.2)
    rw [he]

theorem copyFace_eq_subcollectionRange (S : Finset (Fin (m + 1)))
    (hS : S.Nonempty) :
    copyFace.{v} c u n S =
      subcollectionRange (smallCoefficients c S hS) c u n
        (copyInclusion S hS)
        (JTHigherInterleavedParameter.timeInclusion_injective S hS)
        (smallCoefficient_agrees c n S hS) := by
  ext q z
  cases q using Opposite.rec with
  | op q =>
    cases q using SimplexCategory.rec with
    | _ d =>
      rw [mem_copyFace_iff]
      change (∀ a : Fin (d + 1),
          ((vertexEquiv c u n).symm ((SSet.stdSimplex.objEquiv z).toOrderHom a)).2 ∈ S) ↔
        z ∈ (SSet.Subcomplex.range (SSet.stdSimplex.map
          (coefficientOperator (smallCoefficients c S hS) c u n
            (copyInclusion S hS)
            (JTHigherInterleavedParameter.timeInclusion_injective S hS)
            (smallCoefficient_agrees c n S hS)))).obj _
      rw [JTFiniteCoefficientBridgeOverlap.range_stdMap_iff _
        (coefficientOperator_injective (smallCoefficients c S hS) c u n
          (copyInclusion S hS)
          (JTHigherInterleavedParameter.timeInclusion_injective S hS)
          (smallCoefficient_agrees c n S hS))]
      simp only [copyRange_iff c u n S hS]
      rfl


theorem copyFaceComparison_weak (S : Finset (Fin (m + 1))) :
    WeakEquivalence ((copyFace.{v} c u n S).fromPreimage (prism c u n)) := by
  by_cases hS : S.Nonempty
  · rw [copyFace_eq_subcollectionRange c u n S hS]
    exact subcollectionComparison_weak (smallCoefficients c S hS) c u n
      (copyInclusion S hS)
      (JTHigherInterleavedParameter.timeInclusion_injective S hS)
      (smallCoefficient_agrees c n S hS)
  · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    rw [copyFace_empty]
    let h₀ : IsInitial
        ((((⊥ : (simplex.{v} (bridge k n m)).Subcomplex).preimage (prism c u n)) :
          SSet.{v})) := isInitialBot
    have he : ((⊥ : (simplex.{v} (bridge k n m)).Subcomplex).fromPreimage
        (prism c u n)) = (h₀.uniqueUpToIso isInitialBot).hom := h₀.hom_ext _ _
    rw [he]
    infer_instance

end
end DaggerModels.PartII.JTFiniteCoefficientBridgeCopyFace
