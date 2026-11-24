import DaggerModelsPartII.JTCylinderStaircaseFaces
import Lean.Elab.Tactic.Omega

/-!
# The uncollapsed overlap of adjacent prism staircases

The common chain of cuts `t` and `t+1` is the literal simplex with
vertices `(0,0), …, (0,t), (1,t+1), …, (1,n+1)`. All statements in
this module concern the uncollapsed product `Δ[1] ⊗ Δ[n+1]`.
-/

set_option autoImplicit false

open CategoryTheory Simplicial MonoidalCategory

namespace DaggerModels.PartII.JTCylinderOverlapChains

noncomputable section

open JTCylinderStaircase JTCylinderStaircaseFaces

/-- The common maximal chain of adjacent cuts, with no repeated width. -/
def overlapOrder (n : ℕ) (t : Fin (n + 1)) :
    Fin (n + 2) →o Fin 2 × Fin (n + 2) where
  toFun i := (if i.val ≤ t.val then 0 else 1, i)
  monotone' i j hij := by
    have hv : i.val ≤ j.val := Fin.le_iff_val_le_val.mp hij
    simp only [Prod.mk_le_mk]
    constructor
    · by_cases hi : i.val ≤ t.val
      · by_cases hj : j.val ≤ t.val <;> simp [hi, hj]
      · have hj : ¬ j.val ≤ t.val := by omega
        simp [hi, hj]
    · exact hij

/-- The actual simplex of the common chain in the larger prism. -/
def overlapSimplex (n : ℕ) (t : Fin (n + 1)) :
    (Δ[n + 1] : SSet.{0}) ⟶ (Δ[1] : SSet.{0}) ⊗ Δ[n + 1] :=
  SSet.yonedaEquiv.symm
    (SSet.prodStdSimplex.objEquiv.symm (overlapOrder n t))

/-- The common chain as a subcomplex of the uncollapsed larger prism. -/
def overlapImage (n : ℕ) (t : Fin (n + 1)) :
    ((Δ[1] : SSet.{0}) ⊗ Δ[n + 1]).Subcomplex :=
  SSet.Subcomplex.range (overlapSimplex n t)

theorem overlapImage_eq_ofSimplex (n : ℕ) (t : Fin (n + 1)) :
    overlapImage n t =
      SSet.Subcomplex.ofSimplex (SSet.yonedaEquiv (overlapSimplex n t)) := by
  exact SSet.Subcomplex.range_eq_ofSimplex (overlapSimplex n t)

theorem overlapSimplex_objEquiv (n : ℕ) (t : Fin (n + 1))
    {m : ℕ} (z : (Δ[n + 1] : SSet.{0}).obj (Opposite.op ⦋m⦌)) :
    SSet.prodStdSimplex.objEquiv
        ((overlapSimplex n t).app (Opposite.op ⦋m⦌) z) =
      (overlapOrder n t).comp
        (SSet.stdSimplex.objEquiv z).toOrderHom := by
  apply OrderHom.ext
  funext i
  rfl

/-- The unique face-index map omitting the middle vertex `t+1`. -/
private def overlapFaceHom (n : ℕ) (t : Fin (n + 1)) :
    ⦋n + 1⦌ ⟶ ⦋n + 2⦌ :=
  SimplexCategory.Hom.mk
    ⟨fun i ↦
      ⟨if i.val ≤ t.val then i.val else i.val + 1, by
        change (if i.val ≤ t.val then i.val else i.val + 1) < n + 3
        have hi := i.isLt
        change i.val < n + 2 at hi
        split_ifs <;> omega⟩,
      by
        intro i j hij
        apply Fin.le_iff_val_le_val.mpr
        have hv : i.val ≤ j.val := Fin.le_iff_val_le_val.mp hij
        dsimp
        split_ifs <;> omega⟩

private theorem overlapOrder_left (n : ℕ) (t : Fin (n + 1))
    (i : Fin (n + 2)) :
    staircaseOrder (n + 1) (Fin.castSucc t)
        ((overlapFaceHom n t).toOrderHom i) = overlapOrder n t i := by
  have ht := t.isLt
  have hi := i.isLt
  by_cases hcut : i.val ≤ t.val
  · apply Prod.ext <;> apply Fin.ext <;>
      simp [overlapFaceHom, overlapOrder, staircaseOrder, hcut]
  · have hnext : ¬ i.val + 1 ≤ t.val := by omega
    apply Prod.ext <;> apply Fin.ext <;>
      simp [overlapFaceHom, overlapOrder, staircaseOrder, hcut, hnext]

private theorem overlapOrder_right (n : ℕ) (t : Fin (n + 1))
    (i : Fin (n + 2)) :
    staircaseOrder (n + 1) (Fin.succ t)
        ((overlapFaceHom n t).toOrderHom i) = overlapOrder n t i := by
  have ht := t.isLt
  have hi := i.isLt
  by_cases hcut : i.val ≤ t.val
  · have hright : i.val ≤ t.val + 1 := by omega
    apply Prod.ext <;> apply Fin.ext <;>
      simp [overlapFaceHom, overlapOrder, staircaseOrder, hcut, hright]
  · have hright : ¬ i.val + 1 ≤ t.val + 1 := by omega
    apply Prod.ext <;> apply Fin.ext <;>
      simp [overlapFaceHom, overlapOrder, staircaseOrder, hcut, hright]

/-- The overlap chain is the same missing-middle face of the left cut. -/
theorem overlapSimplex_left (n : ℕ) (t : Fin (n + 1)) :
    overlapSimplex n t =
      SSet.stdSimplex.map (overlapFaceHom n t) ≫
        staircaseSimplex (n + 1) (Fin.castSucc t) := by
  apply SSet.yonedaEquiv.injective
  apply SSet.prodStdSimplex.objEquiv.injective
  apply OrderHom.ext
  funext i
  rw [SSet.yonedaEquiv_comp, SSet.stdSimplex.yonedaEquiv_map]
  simp only [overlapSimplex, staircaseSimplex, Equiv.apply_symm_apply]
  exact (overlapOrder_left n t i).symm

/-- The same overlap chain is the missing-middle face of the right cut. -/
theorem overlapSimplex_right (n : ℕ) (t : Fin (n + 1)) :
    overlapSimplex n t =
      SSet.stdSimplex.map (overlapFaceHom n t) ≫
        staircaseSimplex (n + 1) (Fin.succ t) := by
  apply SSet.yonedaEquiv.injective
  apply SSet.prodStdSimplex.objEquiv.injective
  apply OrderHom.ext
  funext i
  rw [SSet.yonedaEquiv_comp, SSet.stdSimplex.yonedaEquiv_map]
  simp only [overlapSimplex, staircaseSimplex, Equiv.apply_symm_apply]
  exact (overlapOrder_right n t i).symm

/-- Local coordinate form of the accepted staircase at or before its cut. -/
private theorem staircase_lower (k : ℕ) (u : Fin (k + 1))
    (j : Fin (k + 2)) (hj : j.val ≤ u.val) :
    staircaseOrder k u j = (0, ⟨j.val, by omega⟩) := by
  change (if h : j.val ≤ u.val then
    ((0, ⟨j.val, by omega⟩) : Fin 2 × Fin (k + 1)) else
    ((1, ⟨j.val - 1, by omega⟩) : Fin 2 × Fin (k + 1))) =
      ((0, ⟨j.val, by omega⟩) : Fin 2 × Fin (k + 1))
  exact dif_pos hj

/-- Local coordinate form of the accepted staircase after its cut. -/
private theorem staircase_upper (k : ℕ) (u : Fin (k + 1))
    (j : Fin (k + 2)) (hj : ¬ j.val ≤ u.val) :
    staircaseOrder k u j = (1, ⟨j.val - 1, by omega⟩) := by
  change (if h : j.val ≤ u.val then
    ((0, ⟨j.val, by omega⟩) : Fin 2 × Fin (k + 1)) else
    ((1, ⟨j.val - 1, by omega⟩) : Fin 2 × Fin (k + 1))) =
      ((1, ⟨j.val - 1, by omega⟩) : Fin 2 × Fin (k + 1))
  exact dif_neg hj

/-- A simplex in one maximal chain obeys its cut inequalities. -/
private theorem staircase_mem_bounds (k : ℕ) (u : Fin (k + 1))
    {m : ℕ}
    (z : ((Δ[1] : SSet.{0}) ⊗ Δ[k]).obj (Opposite.op ⦋m⦌))
    (hz : z ∈ (staircaseImage k u).obj (Opposite.op ⦋m⦌))
    (i : Fin (m + 1)) :
    ((SSet.prodStdSimplex.objEquiv z i).1 = 0 →
        (SSet.prodStdSimplex.objEquiv z i).2 ≤ u) ∧
      ((SSet.prodStdSimplex.objEquiv z i).1 = 1 →
        u ≤ (SSet.prodStdSimplex.objEquiv z i).2) := by
  obtain ⟨f, hf⟩ :=
    (SSet.Subcomplex.mem_ofSimplex_obj_iff
      (SSet.yonedaEquiv (staircaseSimplex k u)) z).mp hz
  have hp : SSet.prodStdSimplex.objEquiv z i =
      staircaseOrder k u (f.toOrderHom i) := by
    rw [← hf, SSet.prodStdSimplex.objEquiv_map_apply]
    simp only [staircaseSimplex, Equiv.apply_symm_apply]
  constructor
  · intro hzero
    have hi : (f.toOrderHom i).val ≤ u.val :=
      (staircaseOrder_first_iff k u _).mp
        ((congrArg Prod.fst hp).symm.trans hzero)
    rw [staircase_lower k u _ hi] at hp
    have hs := congrArg (fun p : Fin 2 × Fin (k + 1) ↦ p.2.val) hp
    change (SSet.prodStdSimplex.objEquiv z i).2.val =
      (f.toOrderHom i).val at hs
    exact Fin.le_iff_val_le_val.mpr (by omega)
  · intro hone
    have hi : u.val < (f.toOrderHom i).val :=
      (staircaseOrder_second_iff k u _).mp
        ((congrArg Prod.fst hp).symm.trans hone)
    rw [staircase_upper k u _ (Nat.not_le.mpr hi)] at hp
    have hs := congrArg (fun p : Fin 2 × Fin (k + 1) ↦ p.2.val) hp
    change (SSet.prodStdSimplex.objEquiv z i).2.val =
      (f.toOrderHom i).val - 1 at hs
    exact Fin.le_iff_val_le_val.mpr (by omega)

/-- The common-chain image is exactly the intersection of the two
adjacent maximal staircase images, including `n=0,t=0`. -/
theorem overlapImage_eq_inf (n : ℕ) (t : Fin (n + 1)) :
    overlapImage n t =
      staircaseImage (n + 1) (Fin.castSucc t) ⊓
        staircaseImage (n + 1) (Fin.succ t) := by
  apply le_antisymm
  · apply le_inf
    · rw [overlapImage, overlapSimplex_left, staircaseImage,
        ← SSet.Subcomplex.range_eq_ofSimplex]
      exact Subfunctor.range_comp_le _ _
    · rw [overlapImage, overlapSimplex_right, staircaseImage,
        ← SSet.Subcomplex.range_eq_ofSimplex]
      exact Subfunctor.range_comp_le _ _
  · intro q z hz
    induction q using Opposite.rec with | op q =>
      induction q using SimplexCategory.rec with | h m =>
        change z ∈ (staircaseImage (n + 1) (Fin.castSucc t) ⊓
          staircaseImage (n + 1) (Fin.succ t)).obj (Opposite.op ⦋m⦌) at hz
        let c := SSet.prodStdSimplex.objEquiv z
        have hc : ∀ i : Fin (m + 1),
            (c i).1 = if (c i).2.val ≤ t.val then 0 else 1 := by
          intro i
          by_cases hzero : (c i).1 = 0
          · have hle := (staircase_mem_bounds (n + 1) (Fin.castSucc t)
              z hz.1 i).1 hzero
            have hle' : (c i).2.val ≤ t.val := by
              have hv := Fin.le_iff_val_le_val.mp hle
              change (c i).2.val ≤ t.val at hv
              exact hv
            simp [hzero, hle']
          · have hone : (c i).1 = 1 := Fin.eq_one_of_ne_zero _ hzero
            have hle := (staircase_mem_bounds (n + 1) (Fin.succ t)
              z hz.2 i).2 hone
            have hnot : ¬ (c i).2.val ≤ t.val := by
              have hv : t.val + 1 ≤ (c i).2.val := by
                have hv' := Fin.le_iff_val_le_val.mp hle
                change t.val + 1 ≤ (c i).2.val at hv'
                exact hv'
              omega
            simp [hone, hnot]
        change z ∈ (SSet.Subcomplex.range (overlapSimplex n t)).obj
          (Opposite.op ⦋m⦌)
        let w : (Δ[n + 1] : SSet.{0}).obj (Opposite.op ⦋m⦌) :=
          SSet.stdSimplex.objEquiv.symm
            (SimplexCategory.Hom.mk (OrderHom.snd.comp c))
        refine ⟨w, ?_⟩
        apply SSet.prodStdSimplex.objEquiv.injective
        rw [overlapSimplex_objEquiv]
        apply OrderHom.ext
        funext i
        apply Prod.ext
        · simpa only [OrderHom.comp_coe, Function.comp_apply,
            overlapOrder, w, Equiv.apply_symm_apply] using (hc i).symm
        · rfl

end
end DaggerModels.PartII.JTCylinderOverlapChains
