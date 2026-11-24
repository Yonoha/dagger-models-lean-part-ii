import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex
import Lean.Elab.Tactic.Omega

/-!
# Maximal simplices of the uncollapsed standard prism

The `k+1` maximal chains of `Δ[1] ⊗ Δ[k]` cover the uncollapsed prism.
At each successive cut, the new maximal simplex meets the union of its
predecessors in its intersection with the immediately preceding simplex.
The coordinate proof uses the native product-standard-simplex equivalence.
This module concerns the uncollapsed prism and asserts no quotient or
weak-equivalence result.
-/

set_option autoImplicit false

open CategoryTheory Simplicial MonoidalCategory

namespace DaggerModels.PartII.JTCylinderStaircase

/-- The maximal chain
`(0,0), …, (0,t), (1,t), …, (1,k)` in the prism poset. -/
def staircaseOrder (k : ℕ) (t : Fin (k + 1)) :
    Fin (k + 2) →o Fin 2 × Fin (k + 1) where
  toFun i :=
    if hi : i.val ≤ t.val then
      (0, ⟨i.val, by omega⟩)
    else
      (1, ⟨i.val - 1, by omega⟩)
  monotone' i j hij := by
    have hijv : i.val ≤ j.val := Fin.le_iff_val_le_val.mp hij
    dsimp
    split_ifs with hi hj
    all_goals simp only [Prod.mk_le_mk, Fin.mk_le_mk]
    all_goals omega

/-- The `t`th maximal simplex before the two end copies are collapsed. -/
def staircaseSimplex (k : ℕ) (t : Fin (k + 1)) :
    (Δ[k + 1] : SSet.{0}) ⟶ (Δ[1] : SSet.{0}) ⊗ Δ[k] :=
  SSet.yonedaEquiv.symm
    (SSet.prodStdSimplex.objEquiv.symm (staircaseOrder k t))

/-- The image subcomplex of the `t`th maximal prism simplex. -/
def staircaseImage (k : ℕ) (t : Fin (k + 1)) :
    ((Δ[1] : SSet.{0}) ⊗ Δ[k]).Subcomplex :=
  SSet.Subcomplex.ofSimplex (SSet.yonedaEquiv (staircaseSimplex k t))

private theorem staircaseOrder_lower (k : ℕ) (t : Fin (k + 1))
    (j : Fin (k + 2)) (hj : j.val ≤ t.val) :
    staircaseOrder k t j = (0, ⟨j.val, by omega⟩) := by
  change (if hi : j.val ≤ t.val then
    ((0, ⟨j.val, by omega⟩) : Fin 2 × Fin (k + 1)) else
    ((1, ⟨j.val - 1, by omega⟩) : Fin 2 × Fin (k + 1))) =
      ((0, ⟨j.val, by omega⟩) : Fin 2 × Fin (k + 1))
  exact dif_pos hj

private theorem staircaseOrder_upper (k : ℕ) (t : Fin (k + 1))
    (j : Fin (k + 2)) (hj : ¬ j.val ≤ t.val) :
    staircaseOrder k t j = (1, ⟨j.val - 1, by omega⟩) := by
  change (if hi : j.val ≤ t.val then
    ((0, ⟨j.val, by omega⟩) : Fin 2 × Fin (k + 1)) else
    ((1, ⟨j.val - 1, by omega⟩) : Fin 2 × Fin (k + 1))) =
      ((1, ⟨j.val - 1, by omega⟩) : Fin 2 × Fin (k + 1))
  exact dif_neg hj

/-- Coordinate condition for a simplex to lie in one maximal chain. -/
private def Fits (k : ℕ) (t : Fin (k + 1)) {n : ℕ}
    (z : ((Δ[1] : SSet.{0}) ⊗ Δ[k]).obj (Opposite.op ⦋n⦌)) : Prop :=
  ∀ i : Fin (n + 1),
    ((SSet.prodStdSimplex.objEquiv z i).1 = 0 →
      (SSet.prodStdSimplex.objEquiv z i).2 ≤ t) ∧
    ((SSet.prodStdSimplex.objEquiv z i).1 = 1 →
      t ≤ (SSet.prodStdSimplex.objEquiv z i).2)

/-- The existing coordinate-sum map supplies the factor through a maximal
chain whenever its zero and one coordinates obey the cut inequalities. -/
private def coordinateIndex (k : ℕ) {n : ℕ}
    (z : ((Δ[1] : SSet.{0}) ⊗ Δ[k]).obj (Opposite.op ⦋n⦌)) :
    Fin (n + 1) →o Fin (k + 2) :=
  SSet.prodStdSimplex.orderHomOfSimplex z (by omega)

private theorem coordinate_factor (k : ℕ) (t : Fin (k + 1)) {n : ℕ}
    (z : ((Δ[1] : SSet.{0}) ⊗ Δ[k]).obj (Opposite.op ⦋n⦌))
    (hz : Fits k t z) (i : Fin (n + 1)) :
    staircaseOrder k t (coordinateIndex k z i) =
      SSet.prodStdSimplex.objEquiv z i := by
  have h₀ := (hz i).1
  have h₁ := (hz i).2
  by_cases hlevel : z.1 i = 0
  · have hcut : z.2 i ≤ t := h₀ hlevel
    apply Prod.ext
    · apply Fin.ext
      simp [staircaseOrder, coordinateIndex,
        SSet.prodStdSimplex.orderHomOfSimplex, hlevel, hcut]
    · apply Fin.ext
      simp [staircaseOrder, coordinateIndex,
        SSet.prodStdSimplex.orderHomOfSimplex, hlevel, hcut]
  · have hlevel₁ : z.1 i = 1 := Fin.eq_one_of_ne_zero _ hlevel
    have hcut : t ≤ z.2 i := h₁ hlevel₁
    have hnot : ¬ 1 + (z.2 i).val ≤ t.val := by
      omega
    apply Prod.ext
    · apply Fin.ext
      simp [staircaseOrder, coordinateIndex,
        SSet.prodStdSimplex.orderHomOfSimplex, hlevel₁, hnot]
    · apply Fin.ext
      simp [staircaseOrder, coordinateIndex,
        SSet.prodStdSimplex.orderHomOfSimplex, hlevel₁, hnot]

/-- Membership in the image of a maximal simplex is exactly the two
coordinate inequalities at every vertex of the given simplex. -/
private theorem mem_staircaseImage_iff (k : ℕ) (t : Fin (k + 1)) {n : ℕ}
    (z : ((Δ[1] : SSet.{0}) ⊗ Δ[k]).obj (Opposite.op ⦋n⦌)) :
    z ∈ (staircaseImage k t).obj (Opposite.op ⦋n⦌) ↔ Fits k t z := by
  constructor
  · intro hz i
    obtain ⟨f, hf⟩ :=
      (SSet.Subcomplex.mem_ofSimplex_obj_iff
        (SSet.yonedaEquiv (staircaseSimplex k t)) z).mp hz
    have hp : SSet.prodStdSimplex.objEquiv z i =
        staircaseOrder k t (f.toOrderHom i) := by
      rw [← hf, SSet.prodStdSimplex.objEquiv_map_apply]
      simp only [staircaseSimplex, Equiv.apply_symm_apply]
    constructor
    · intro hzero
      by_cases hi : (f.toOrderHom i).val ≤ t.val
      · rw [staircaseOrder_lower k t _ hi] at hp
        have hs := congrArg (fun p : Fin 2 × Fin (k + 1) ↦ p.2.val) hp
        dsimp at hs
        change z.2 i ≤ t
        exact Fin.le_iff_val_le_val.mpr (by omega)
      · rw [staircaseOrder_upper k t _ hi] at hp
        have hs := congrArg (fun p : Fin 2 × Fin (k + 1) ↦ p.1) hp
        exact False.elim ((by decide : (0 : Fin 2) ≠ 1) (hzero.symm.trans hs))
    · intro hone
      by_cases hi : (f.toOrderHom i).val ≤ t.val
      · rw [staircaseOrder_lower k t _ hi] at hp
        have hs := congrArg (fun p : Fin 2 × Fin (k + 1) ↦ p.1) hp
        exact False.elim ((by decide : (1 : Fin 2) ≠ 0) (hone.symm.trans hs))
      · rw [staircaseOrder_upper k t _ hi] at hp
        have hs := congrArg (fun p : Fin 2 × Fin (k + 1) ↦ p.2.val) hp
        dsimp at hs
        change t ≤ z.2 i
        exact Fin.le_iff_val_le_val.mpr (by omega)
  · intro hz
    apply (SSet.Subcomplex.mem_ofSimplex_obj_iff
      (SSet.yonedaEquiv (staircaseSimplex k t)) z).mpr
    refine ⟨SimplexCategory.Hom.mk (coordinateIndex k z), ?_⟩
    apply SSet.prodStdSimplex.objEquiv.injective
    apply OrderHom.ext
    funext i
    rw [SSet.prodStdSimplex.objEquiv_map_apply]
    simpa only [staircaseSimplex, Equiv.apply_symm_apply] using
      (coordinate_factor k t z hz i)

/-- Every prism simplex factors through a maximal staircase simplex. -/
private theorem staircase_cover_obj (k n : ℕ)
    (z : ((Δ[1] : SSet.{0}) ⊗ Δ[k]).obj (Opposite.op ⦋n⦌)) :
    ∃ t : Fin (k + 1),
      z ∈ (staircaseImage k t).obj (Opposite.op ⦋n⦌) := by
  classical
  let c := SSet.prodStdSimplex.objEquiv z
  let zeros : Finset (Fin (n + 1)) := Finset.univ.filter (fun i ↦ (c i).1 = 0)
  by_cases hz : zeros.Nonempty
  · let i₀ : Fin (n + 1) := zeros.max' hz
    have hi₀ : (c i₀).1 = 0 := by
      have hm : i₀ ∈ zeros := Finset.max'_mem zeros hz
      simpa only [zeros, Finset.mem_filter, Finset.mem_univ, true_and] using hm
    let t : Fin (k + 1) := (c i₀).2
    refine ⟨t, (mem_staircaseImage_iff k t z).2 ?_⟩
    intro i
    constructor
    · intro hzero
      have himem : i ∈ zeros := by
        simp only [zeros, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hzero
      have hle : i ≤ i₀ := Finset.le_max' zeros i himem
      exact (c.monotone hle).2
    · intro hone
      have hle : i₀ ≤ i := by
        by_contra hn
        have hlt : i < i₀ := by omega
        have hbad := (c.monotone hlt.le).1
        rw [hone, hi₀] at hbad
        exact (by decide : ¬ ((1 : Fin 2) ≤ 0)) hbad
      exact (c.monotone hle).2
  · refine ⟨0, (mem_staircaseImage_iff k 0 z).2 ?_⟩
    intro i
    constructor
    · intro hzero
      have himem : i ∈ zeros := by
        simp only [zeros, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hzero
      exact False.elim (hz ⟨i, himem⟩)
    · intro _
      exact bot_le

/-- The `k+1` explicit maximal simplices cover the uncollapsed prism. -/
theorem staircase_cover (k : ℕ) :
    (⨆ t : Fin (k + 1), staircaseImage k t) = ⊤ := by
  ext q z
  induction q using Opposite.rec with | op q =>
    induction q using SimplexCategory.rec with | h n =>
      simp only [Subfunctor.iSup_obj, Set.mem_iUnion]
      exact ⟨fun _ ↦ trivial, fun _ ↦ staircase_cover_obj k n z⟩

/-- The union of the maximal simplices before a given cut. -/
def previous (k : ℕ) (t : Fin (k + 1)) :
    ((Δ[1] : SSet.{0}) ⊗ Δ[k]).Subcomplex :=
  ⨆ s : {s : Fin (k + 1) // s.val < t.val}, staircaseImage k s.val

/-- The new maximal simplex meets all earlier ones in its immediately
preceding face. This is an equality in the uncollapsed prism. -/
theorem staircase_adjacent (k : ℕ) (t : Fin (k + 1)) (ht : 0 < t.val) :
    staircaseImage k t ⊓ previous k t =
      staircaseImage k t ⊓
        staircaseImage k ⟨t.val - 1, by omega⟩ := by
  let p : Fin (k + 1) := ⟨t.val - 1, by omega⟩
  have hp : p.val < t.val := by dsimp [p]; omega
  ext q z
  induction q using Opposite.rec with | op q =>
    induction q using SimplexCategory.rec with | h n =>
      change z ∈ (staircaseImage k t ⊓ previous k t).obj (Opposite.op ⦋n⦌) ↔
        z ∈ (staircaseImage k t ⊓ staircaseImage k p).obj (Opposite.op ⦋n⦌)
      simp only [Subfunctor.min_obj, previous, Subfunctor.iSup_obj,
        Set.mem_inter_iff, Set.mem_iUnion]
      constructor
      · rintro ⟨hnew, ⟨s, hold⟩⟩
        have hn := (mem_staircaseImage_iff k t z).1 hnew
        have ho := (mem_staircaseImage_iff k s.val z).1 hold
        refine ⟨hnew, (mem_staircaseImage_iff k p z).2 ?_⟩
        intro i
        constructor
        · intro hzero
          have hle := (ho i).1 hzero
          apply Fin.le_iff_val_le_val.mpr
          have hs : s.val.val < t.val := s.property
          simp only [SSet.prodStdSimplex.objEquiv_apply_snd] at hle ⊢
          dsimp [p]
          omega
        · intro hone
          have hle := (hn i).2 hone
          apply Fin.le_iff_val_le_val.mpr
          simp only [SSet.prodStdSimplex.objEquiv_apply_snd] at hle ⊢
          dsimp [p]
          omega
      · rintro ⟨hnew, hold⟩
        exact ⟨hnew, ⟨⟨p, hp⟩, hold⟩⟩

end DaggerModels.PartII.JTCylinderStaircase
