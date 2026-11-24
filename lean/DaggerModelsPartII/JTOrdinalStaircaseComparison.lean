import DaggerModelsPartII.JTCylinderStaircase
import Lean.Elab.Tactic.Omega

/-! Actual simplex operators for successive cuts of a staircase comparison. -/

set_option autoImplicit false

open CategoryTheory Simplicial

namespace DaggerModels.PartII.JTOrdinalStaircaseComparison

open JTCylinderStaircase

/-- Insert the lower cut vertex. -/
def before (K : SimplexCategory) (t : Fin (K.len + 1)) :
    K ⟶ ⦋K.len + 1⦌ :=
  SimplexCategory.Hom.mk ⟨fun u ↦
    ⟨if u.val ≤ t.val then u.val else u.val + 1, by
      change (if u.val ≤ t.val then u.val else u.val + 1) < K.len + 2
      split_ifs <;> omega⟩, by
      intro u v huv
      change u.val ≤ v.val at huv
      change (if u.val ≤ t.val then u.val else u.val + 1) ≤
        (if v.val ≤ t.val then v.val else v.val + 1)
      split_ifs <;> omega⟩

/-- Insert the upper cut vertex. -/
def after (K : SimplexCategory) (t : Fin (K.len + 1)) :
    K ⟶ ⦋K.len + 1⦌ :=
  SimplexCategory.Hom.mk ⟨fun u ↦
    ⟨if u.val < t.val then u.val else u.val + 1, by
      change (if u.val < t.val then u.val else u.val + 1) < K.len + 2
      split_ifs <;> omega⟩, by
      intro u v huv
      change u.val ≤ v.val at huv
      change (if u.val < t.val then u.val else u.val + 1) ≤
        (if v.val < t.val then v.val else v.val + 1)
      split_ifs <;> omega⟩

theorem before_staircase (K : SimplexCategory) (t : Fin (K.len + 1))
    (u : Fin (K.len + 1)) :
    staircaseOrder K.len t ((before K t).toOrderHom u) =
      (if u.val ≤ t.val then (0, u) else (1, u)) := by
  by_cases hu : u.val ≤ t.val
  · have hb : ((before K t).toOrderHom u).val = u.val := by
      dsimp [before]
      exact if_pos hu
    have hc : ((before K t).toOrderHom u).val ≤ t.val := hb ▸ hu
    simp only [if_pos hu]
    change (if hi : ((before K t).toOrderHom u).val ≤ t.val then
      ((0, ⟨((before K t).toOrderHom u).val, by omega⟩) :
        Fin 2 × Fin (K.len + 1)) else
      (1, ⟨((before K t).toOrderHom u).val - 1, by omega⟩)) = (0, u)
    rw [dif_pos hc]
    apply Prod.ext
    · rfl
    · apply Fin.ext
      change ((before K t).toOrderHom u).val = u.val
      omega
  · have hb : ((before K t).toOrderHom u).val = u.val + 1 := by
      dsimp [before]
      exact if_neg hu
    have hc : ¬ ((before K t).toOrderHom u).val ≤ t.val := by omega
    simp only [if_neg hu]
    change (if hi : ((before K t).toOrderHom u).val ≤ t.val then
      ((0, ⟨((before K t).toOrderHom u).val, by omega⟩) :
        Fin 2 × Fin (K.len + 1)) else
      (1, ⟨((before K t).toOrderHom u).val - 1, by omega⟩)) = (1, u)
    rw [dif_neg hc]
    apply Prod.ext
    · rfl
    · apply Fin.ext
      change ((before K t).toOrderHom u).val - 1 = u.val
      omega

theorem after_staircase (K : SimplexCategory) (t : Fin (K.len + 1))
    (u : Fin (K.len + 1)) :
    staircaseOrder K.len t ((after K t).toOrderHom u) =
      (if u.val < t.val then (0, u) else (1, u)) := by
  by_cases hu : u.val < t.val
  · have hb : ((after K t).toOrderHom u).val = u.val := by
      dsimp [after]
      exact if_pos hu
    have hc : ((after K t).toOrderHom u).val ≤ t.val := by omega
    simp only [if_pos hu]
    change (if hi : ((after K t).toOrderHom u).val ≤ t.val then
      ((0, ⟨((after K t).toOrderHom u).val, by omega⟩) :
        Fin 2 × Fin (K.len + 1)) else
      (1, ⟨((after K t).toOrderHom u).val - 1, by omega⟩)) = (0, u)
    rw [dif_pos hc]
    apply Prod.ext
    · rfl
    · apply Fin.ext
      omega
  · have hb : ((after K t).toOrderHom u).val = u.val + 1 := by
      dsimp [after]
      exact if_neg hu
    have hc : ¬ ((after K t).toOrderHom u).val ≤ t.val := by omega
    simp only [if_neg hu]
    change (if hi : ((after K t).toOrderHom u).val ≤ t.val then
      ((0, ⟨((after K t).toOrderHom u).val, by omega⟩) :
        Fin 2 × Fin (K.len + 1)) else
      (1, ⟨((after K t).toOrderHom u).val - 1, by omega⟩)) = (1, u)
    rw [dif_neg hc]
    apply Prod.ext
    · rfl
    · apply Fin.ext
      change ((after K t).toOrderHom u).val - 1 = u.val
      omega

/-- Pointwise ordered maps on two rows define a monotone path on the staircase. -/
def path (K B : SimplexCategory) (f₀ f₁ : K ⟶ B)
    (h : ∀ u : Fin (K.len + 1), f₀.toOrderHom u ≤ f₁.toOrderHom u)
    (t : Fin (K.len + 1)) : ⦋K.len + 1⦌ ⟶ B :=
  SimplexCategory.Hom.mk ⟨fun v ↦
    if (staircaseOrder K.len t v).1 = 0 then
      f₀.toOrderHom (staircaseOrder K.len t v).2
    else f₁.toOrderHom (staircaseOrder K.len t v).2, by
      intro u v huv
      have hs := (staircaseOrder K.len t).monotone huv
      obtain ⟨hfirst, hsecond⟩ := (Prod.mk_le_mk).mp hs
      have hf := f₀.toOrderHom.monotone hsecond
      have hg := f₁.toOrderHom.monotone hsecond
      by_cases hu : (staircaseOrder K.len t u).1 = 0
      · by_cases hv : (staircaseOrder K.len t v).1 = 0
        · simp only [if_pos hu, if_pos hv]
          exact hf
        · simp only [if_pos hu, if_neg hv]
          exact (h _).trans hg
      · by_cases hv : (staircaseOrder K.len t v).1 = 0
        · have hupper : (staircaseOrder K.len t u).1 = 1 :=
            Fin.eq_one_of_ne_zero _ hu
          change (staircaseOrder K.len t u).1 ≤
            (staircaseOrder K.len t v).1 at hfirst
          rw [hupper, hv] at hfirst
          have hbad : ¬ ((1 : Fin 2) ≤ 0) := by decide
          have : False := hbad hfirst
          exact this.elim
        · simp only [if_neg hu, if_neg hv]
          exact hg⟩

theorem before_path (K B : SimplexCategory) (f₀ f₁ : K ⟶ B)
    (h : ∀ u : Fin (K.len + 1), f₀.toOrderHom u ≤ f₁.toOrderHom u)
    (t u : Fin (K.len + 1)) :
    (before K t ≫ path K B f₀ f₁ h t).toOrderHom u =
      if u.val ≤ t.val then f₀.toOrderHom u else f₁.toOrderHom u := by
  change (if (staircaseOrder K.len t ((before K t).toOrderHom u)).1 = 0 then
    f₀.toOrderHom (staircaseOrder K.len t ((before K t).toOrderHom u)).2 else
    f₁.toOrderHom (staircaseOrder K.len t ((before K t).toOrderHom u)).2) = _
  rw [before_staircase]
  by_cases hu : u.val ≤ t.val <;> simp [hu]

theorem after_path (K B : SimplexCategory) (f₀ f₁ : K ⟶ B)
    (h : ∀ u : Fin (K.len + 1), f₀.toOrderHom u ≤ f₁.toOrderHom u)
    (t u : Fin (K.len + 1)) :
    (after K t ≫ path K B f₀ f₁ h t).toOrderHom u =
      if u.val < t.val then f₀.toOrderHom u else f₁.toOrderHom u := by
  change (if (staircaseOrder K.len t ((after K t).toOrderHom u)).1 = 0 then
    f₀.toOrderHom (staircaseOrder K.len t ((after K t).toOrderHom u)).2 else
    f₁.toOrderHom (staircaseOrder K.len t ((after K t).toOrderHom u)).2) = _
  rw [after_staircase]
  by_cases hu : u.val < t.val <;> simp [hu]

theorem plateau (K B : SimplexCategory) (f₀ f₁ : K ⟶ B)
    (h : ∀ u : Fin (K.len + 1), f₀.toOrderHom u ≤ f₁.toOrderHom u)
    (t u : Fin (K.len + 1))
    (heq : f₀.toOrderHom u = f₁.toOrderHom u) :
    (before K t ≫ path K B f₀ f₁ h t).toOrderHom u =
      (after K t ≫ path K B f₀ f₁ h t).toOrderHom u := by
  rw [before_path, after_path]
  by_cases hb : u.val ≤ t.val
  · by_cases ha : u.val < t.val
    · simp [hb, ha]
    · simp [hb, ha, heq]
  · have ha : ¬ u.val < t.val := by omega
    simp [hb, ha]

theorem adjacent (K B : SimplexCategory) (f₀ f₁ : K ⟶ B)
    (h : ∀ u : Fin (K.len + 1), f₀.toOrderHom u ≤ f₁.toOrderHom u)
    (t t' : Fin (K.len + 1)) (htt' : t.val + 1 = t'.val) :
    before K t ≫ path K B f₀ f₁ h t =
      after K t' ≫ path K B f₀ f₁ h t' := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext u
  rw [before_path, after_path]
  have hiff : u.val ≤ t.val ↔ u.val < t'.val := by omega
  by_cases hu : u.val ≤ t.val
  · simp [hu, hiff.mp hu]
  · have hnot : ¬ u.val < t'.val := by omega
    simp [hu, hnot]

theorem first_endpoint (K B : SimplexCategory) (f₀ f₁ : K ⟶ B)
    (h : ∀ u : Fin (K.len + 1), f₀.toOrderHom u ≤ f₁.toOrderHom u) :
    after K 0 ≫ path K B f₀ f₁ h 0 = f₁ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext u
  rw [after_path]
  simp

theorem last_endpoint (K B : SimplexCategory) (f₀ f₁ : K ⟶ B)
    (h : ∀ u : Fin (K.len + 1), f₀.toOrderHom u ≤ f₁.toOrderHom u) :
    before K (Fin.last K.len) ≫ path K B f₀ f₁ h (Fin.last K.len) = f₀ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext u
  rw [before_path]
  have hu : u.val ≤ K.len := by
    have hbound := u.isLt
    omega
  change (if u.val ≤ K.len then f₀.toOrderHom u else f₁.toOrderHom u) = _
  rw [if_pos hu]

end DaggerModels.PartII.JTOrdinalStaircaseComparison
