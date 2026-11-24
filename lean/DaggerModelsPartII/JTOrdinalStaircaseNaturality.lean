import DaggerModelsPartII.JTOrdinalStaircaseComparison
import DaggerModelsPartII.JTCylinderStaircaseFaces
import Lean.Elab.Tactic.Omega

/-! Phase-preserving transport of the actual staircase ordinals. -/

set_option autoImplicit false

open CategoryTheory Simplicial

namespace DaggerModels.PartII.JTOrdinalStaircaseNaturality

open JTOrdinalStaircaseComparison JTCylinderStaircase
open JTCylinderStaircaseFaces

/-- The row-preserving map between the actual staircase ordinals. -/
def map (K K' : SimplexCategory) (a : K ⟶ K')
    (t : Fin (K.len + 1)) : ⦋K.len + 1⦌ ⟶ ⦋K'.len + 1⦌ :=
  SimplexCategory.Hom.mk ⟨fun v ↦
    if (staircaseOrder K.len t v).1 = 0 then
      Fin.castSucc (a.toOrderHom (staircaseOrder K.len t v).2)
    else Fin.succ (a.toOrderHom (staircaseOrder K.len t v).2), by
      intro u v huv
      have hs := (staircaseOrder K.len t).monotone huv
      obtain ⟨hfirst, hsecond⟩ := (Prod.mk_le_mk).mp hs
      have ha := a.toOrderHom.monotone hsecond
      by_cases hu : (staircaseOrder K.len t u).1 = 0
      · by_cases hv : (staircaseOrder K.len t v).1 = 0
        · simp only [if_pos hu, if_pos hv]
          exact Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp ha)
        · simp only [if_pos hu, if_neg hv]
          change (a.toOrderHom (staircaseOrder K.len t u).2).val ≤
            (a.toOrderHom (staircaseOrder K.len t v).2).val + 1
          exact Nat.le_succ_of_le (Fin.le_iff_val_le_val.mp ha)
      · by_cases hv : (staircaseOrder K.len t v).1 = 0
        · have hupper : (staircaseOrder K.len t u).1 = 1 :=
            Fin.eq_one_of_ne_zero _ hu
          change (staircaseOrder K.len t u).1 ≤
            (staircaseOrder K.len t v).1 at hfirst
          rw [hupper, hv] at hfirst
          exact False.elim ((by decide : ¬ ((1 : Fin 2) ≤ 0)) hfirst)
        · simp only [if_neg hu, if_neg hv]
          apply Fin.le_iff_val_le_val.mpr
          change (a.toOrderHom (staircaseOrder K.len t u).2).val + 1 ≤
            (a.toOrderHom (staircaseOrder K.len t v).2).val + 1
          exact Nat.add_le_add_right (Fin.le_iff_val_le_val.mp ha) 1⟩

private theorem first_width_le (K : SimplexCategory) (t : Fin (K.len + 1))
    (v : Fin (K.len + 2)) (hv : (staircaseOrder K.len t v).1 = 0) :
    (staircaseOrder K.len t v).2 ≤ t := by
  have hcut : v.val ≤ t.val := (staircaseOrder_first_iff K.len t v).mp hv
  simp only [staircaseOrder, OrderHom.coe_mk, dif_pos hcut]
  exact Fin.le_iff_val_le_val.mpr hcut

private theorem cut_le_second_width (K : SimplexCategory) (t : Fin (K.len + 1))
    (v : Fin (K.len + 2)) (hv : (staircaseOrder K.len t v).1 = 1) :
    t ≤ (staircaseOrder K.len t v).2 := by
  have hcut : t.val < v.val := (staircaseOrder_second_iff K.len t v).mp hv
  have hnot : ¬ v.val ≤ t.val := by omega
  simp only [staircaseOrder, OrderHom.coe_mk, dif_neg hnot]
  apply Fin.le_iff_val_le_val.mpr
  change t.val ≤ v.val - 1
  omega

/-- Both prism coordinates are transported exactly, even if `a` identifies vertices. -/
theorem staircaseOrder_map (K K' : SimplexCategory) (a : K ⟶ K')
    (t : Fin (K.len + 1)) (v : Fin (K.len + 2)) :
    staircaseOrder K'.len (a.toOrderHom t) ((map K K' a t).toOrderHom v) =
      ((staircaseOrder K.len t v).1,
        a.toOrderHom (staircaseOrder K.len t v).2) := by
  let p := staircaseOrder K.len t v
  by_cases hp : p.1 = 0
  · have hwidth : p.2 ≤ t := first_width_le K t v hp
    have htarget : (a.toOrderHom p.2).val ≤ (a.toOrderHom t).val :=
      Fin.le_iff_val_le_val.mp (a.toOrderHom.monotone hwidth)
    have hm : ((map K K' a t).toOrderHom v).val =
        (a.toOrderHom p.2).val := by
      change (if p.1 = 0 then Fin.castSucc (a.toOrderHom p.2)
        else Fin.succ (a.toOrderHom p.2)).val = _
      rw [if_pos hp]
      rfl
    have hc : ((map K K' a t).toOrderHom v).val ≤
        (a.toOrderHom t).val := by omega
    change (if h : ((map K K' a t).toOrderHom v).val ≤
        (a.toOrderHom t).val then
      ((0, ⟨((map K K' a t).toOrderHom v).val, by omega⟩) :
        Fin 2 × Fin (K'.len + 1)) else
      (1, ⟨((map K K' a t).toOrderHom v).val - 1, by omega⟩)) =
        (p.1, a.toOrderHom p.2)
    rw [dif_pos hc]
    apply Prod.ext
    · exact hp.symm
    · apply Fin.ext
      change ((map K K' a t).toOrderHom v).val = (a.toOrderHom p.2).val
      exact hm
  · have hp' : p.1 = 1 := Fin.eq_one_of_ne_zero _ hp
    have hwidth : t ≤ p.2 := cut_le_second_width K t v hp'
    have htarget : (a.toOrderHom t).val ≤ (a.toOrderHom p.2).val :=
      Fin.le_iff_val_le_val.mp (a.toOrderHom.monotone hwidth)
    have hm : ((map K K' a t).toOrderHom v).val =
        (a.toOrderHom p.2).val + 1 := by
      change (if p.1 = 0 then Fin.castSucc (a.toOrderHom p.2)
        else Fin.succ (a.toOrderHom p.2)).val = _
      rw [if_neg hp]
      rfl
    have hc : ¬ ((map K K' a t).toOrderHom v).val ≤
        (a.toOrderHom t).val := by omega
    change (if h : ((map K K' a t).toOrderHom v).val ≤
        (a.toOrderHom t).val then
      ((0, ⟨((map K K' a t).toOrderHom v).val, by omega⟩) :
        Fin 2 × Fin (K'.len + 1)) else
      (1, ⟨((map K K' a t).toOrderHom v).val - 1, by omega⟩)) =
        (p.1, a.toOrderHom p.2)
    rw [dif_neg hc]
    apply Prod.ext
    · exact hp'.symm
    · apply Fin.ext
      change ((map K K' a t).toOrderHom v).val - 1 =
        (a.toOrderHom p.2).val
      omega

/-- A commuting square on each row transports the entire staircase path. -/
theorem path_map (K K' B B' : SimplexCategory)
    (a : K ⟶ K') (b : B ⟶ B')
    (f₀ f₁ : K ⟶ B) (g₀ g₁ : K' ⟶ B')
    (h : ∀ u : Fin (K.len + 1), f₀.toOrderHom u ≤ f₁.toOrderHom u)
    (h' : ∀ u : Fin (K'.len + 1), g₀.toOrderHom u ≤ g₁.toOrderHom u)
    (hs₀ : f₀ ≫ b = a ≫ g₀) (hs₁ : f₁ ≫ b = a ≫ g₁)
    (t : Fin (K.len + 1)) :
    map K K' a t ≫ path K' B' g₀ g₁ h' (a.toOrderHom t) =
      path K B f₀ f₁ h t ≫ b := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext v
  let p := staircaseOrder K.len t v
  have hcoord := staircaseOrder_map K K' a t v
  change (if (staircaseOrder K'.len (a.toOrderHom t)
        ((map K K' a t).toOrderHom v)).1 = 0 then
      g₀.toOrderHom (staircaseOrder K'.len (a.toOrderHom t)
        ((map K K' a t).toOrderHom v)).2
      else g₁.toOrderHom (staircaseOrder K'.len (a.toOrderHom t)
        ((map K K' a t).toOrderHom v)).2) =
    b.toOrderHom (if p.1 = 0 then f₀.toOrderHom p.2 else f₁.toOrderHom p.2)
  rw [hcoord]
  change (if p.1 = 0 then g₀.toOrderHom (a.toOrderHom p.2)
    else g₁.toOrderHom (a.toOrderHom p.2)) =
      b.toOrderHom (if p.1 = 0 then f₀.toOrderHom p.2 else f₁.toOrderHom p.2)
  by_cases hp : p.1 = 0
  · simp only [if_pos hp]
    have hs := congrArg (fun q : K ⟶ B' ↦ q.toOrderHom p.2) hs₀
    change b.toOrderHom (f₀.toOrderHom p.2) =
      g₀.toOrderHom (a.toOrderHom p.2) at hs
    exact hs.symm
  · simp only [if_neg hp]
    have hs := congrArg (fun q : K ⟶ B' ↦ q.toOrderHom p.2) hs₁
    change b.toOrderHom (f₁.toOrderHom p.2) =
      g₁.toOrderHom (a.toOrderHom p.2) at hs
    exact hs.symm

/-- The lower embedding is natural if no vertex strictly above the cut
is identified with the image of the cut. -/
theorem map_before_of_strict_right (K K' : SimplexCategory) (a : K ⟶ K')
    (t : Fin (K.len + 1))
    (hstrict : ∀ u : Fin (K.len + 1), t < u →
      a.toOrderHom t < a.toOrderHom u) :
    before K t ≫ map K K' a t =
      a ≫ before K' (a.toOrderHom t) := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext u
  apply (staircaseOrder_injective K'.len (a.toOrderHom t))
  change staircaseOrder K'.len (a.toOrderHom t)
      ((map K K' a t).toOrderHom ((before K t).toOrderHom u)) =
    staircaseOrder K'.len (a.toOrderHom t)
      ((before K' (a.toOrderHom t)).toOrderHom (a.toOrderHom u))
  rw [staircaseOrder_map, before_staircase, before_staircase]
  by_cases hu : u.val ≤ t.val
  · have ha : (a.toOrderHom u).val ≤ (a.toOrderHom t).val :=
      Fin.le_iff_val_le_val.mp
        (a.toOrderHom.monotone (Fin.le_iff_val_le_val.mpr hu))
    simp [hu, ha]
  · have htu : t < u := Fin.lt_def.mpr (by omega)
    have ha : ¬ (a.toOrderHom u).val ≤ (a.toOrderHom t).val := by
      have hlt := hstrict u htu
      exact Nat.not_le_of_gt (Fin.lt_def.mp hlt)
    simp [hu, ha]

/-- The upper embedding is natural if no vertex strictly below the cut
is identified with the image of the cut. -/
theorem map_after_of_strict_left (K K' : SimplexCategory) (a : K ⟶ K')
    (t : Fin (K.len + 1))
    (hstrict : ∀ u : Fin (K.len + 1), u < t →
      a.toOrderHom u < a.toOrderHom t) :
    after K t ≫ map K K' a t =
      a ≫ after K' (a.toOrderHom t) := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext u
  apply (staircaseOrder_injective K'.len (a.toOrderHom t))
  change staircaseOrder K'.len (a.toOrderHom t)
      ((map K K' a t).toOrderHom ((after K t).toOrderHom u)) =
    staircaseOrder K'.len (a.toOrderHom t)
      ((after K' (a.toOrderHom t)).toOrderHom (a.toOrderHom u))
  rw [staircaseOrder_map, after_staircase, after_staircase]
  by_cases hu : u.val < t.val
  · have ha : (a.toOrderHom u).val < (a.toOrderHom t).val :=
      Fin.lt_def.mp (hstrict u (Fin.lt_def.mpr hu))
    simp [hu, ha]
  · have htu : t ≤ u := Fin.le_iff_val_le_val.mpr (by omega)
    have ha : ¬ (a.toOrderHom u).val < (a.toOrderHom t).val := by
      have hle := a.toOrderHom.monotone htu
      exact Nat.not_lt_of_ge (Fin.le_iff_val_le_val.mp hle)
    simp [hu, ha]

/-- The lower embedding keeps its source phase at every vertex. -/
theorem map_before_coordinates (K K' : SimplexCategory) (a : K ⟶ K')
    (t u : Fin (K.len + 1)) :
    staircaseOrder K'.len (a.toOrderHom t)
        ((before K t ≫ map K K' a t).toOrderHom u) =
      if u.val ≤ t.val then (0, a.toOrderHom u) else (1, a.toOrderHom u) := by
  change staircaseOrder K'.len (a.toOrderHom t)
    ((map K K' a t).toOrderHom ((before K t).toOrderHom u)) = _
  rw [staircaseOrder_map, before_staircase]
  by_cases hu : u.val ≤ t.val <;> simp [hu]

/-- The upper embedding keeps its source phase at every vertex. -/
theorem map_after_coordinates (K K' : SimplexCategory) (a : K ⟶ K')
    (t u : Fin (K.len + 1)) :
    staircaseOrder K'.len (a.toOrderHom t)
        ((after K t ≫ map K K' a t).toOrderHom u) =
      if u.val < t.val then (0, a.toOrderHom u) else (1, a.toOrderHom u) := by
  change staircaseOrder K'.len (a.toOrderHom t)
    ((map K K' a t).toOrderHom ((after K t).toOrderHom u)) = _
  rw [staircaseOrder_map, after_staircase]
  by_cases hu : u.val < t.val <;> simp [hu]

/-- A target path along the mapped lower embedding uses the source cut. -/
theorem map_before_path (K K' B : SimplexCategory) (a : K ⟶ K')
    (g₀ g₁ : K' ⟶ B)
    (h : ∀ u : Fin (K'.len + 1), g₀.toOrderHom u ≤ g₁.toOrderHom u)
    (t u : Fin (K.len + 1)) :
    (before K t ≫ map K K' a t ≫
      path K' B g₀ g₁ h (a.toOrderHom t)).toOrderHom u =
        if u.val ≤ t.val then g₀.toOrderHom (a.toOrderHom u)
        else g₁.toOrderHom (a.toOrderHom u) := by
  change (if (staircaseOrder K'.len (a.toOrderHom t)
      ((before K t ≫ map K K' a t).toOrderHom u)).1 = 0 then
    g₀.toOrderHom (staircaseOrder K'.len (a.toOrderHom t)
      ((before K t ≫ map K K' a t).toOrderHom u)).2 else
    g₁.toOrderHom (staircaseOrder K'.len (a.toOrderHom t)
      ((before K t ≫ map K K' a t).toOrderHom u)).2) = _
  rw [map_before_coordinates]
  by_cases hu : u.val ≤ t.val <;> simp [hu]

/-- A target path along the mapped upper embedding uses the source cut. -/
theorem map_after_path (K K' B : SimplexCategory) (a : K ⟶ K')
    (g₀ g₁ : K' ⟶ B)
    (h : ∀ u : Fin (K'.len + 1), g₀.toOrderHom u ≤ g₁.toOrderHom u)
    (t u : Fin (K.len + 1)) :
    (after K t ≫ map K K' a t ≫
      path K' B g₀ g₁ h (a.toOrderHom t)).toOrderHom u =
        if u.val < t.val then g₀.toOrderHom (a.toOrderHom u)
        else g₁.toOrderHom (a.toOrderHom u) := by
  change (if (staircaseOrder K'.len (a.toOrderHom t)
      ((after K t ≫ map K K' a t).toOrderHom u)).1 = 0 then
    g₀.toOrderHom (staircaseOrder K'.len (a.toOrderHom t)
      ((after K t ≫ map K K' a t).toOrderHom u)).2 else
    g₁.toOrderHom (staircaseOrder K'.len (a.toOrderHom t)
      ((after K t ≫ map K K' a t).toOrderHom u)).2) = _
  rw [map_after_coordinates]
  by_cases hu : u.val < t.val <;> simp [hu]

/-- A collapsed right-side vertex is harmless after applying a path
when the two target rows agree there. -/
theorem before_path_plateau (K K' B : SimplexCategory) (a : K ⟶ K')
    (g₀ g₁ : K' ⟶ B)
    (h : ∀ u : Fin (K'.len + 1), g₀.toOrderHom u ≤ g₁.toOrderHom u)
    (t : Fin (K.len + 1))
    (hplateau : ∀ u : Fin (K.len + 1), t < u →
      a.toOrderHom u = a.toOrderHom t →
      g₀.toOrderHom (a.toOrderHom u) = g₁.toOrderHom (a.toOrderHom u)) :
    before K t ≫ map K K' a t ≫ path K' B g₀ g₁ h (a.toOrderHom t) =
      a ≫ before K' (a.toOrderHom t) ≫
        path K' B g₀ g₁ h (a.toOrderHom t) := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext u
  rw [map_before_path]
  change (if u.val ≤ t.val then g₀.toOrderHom (a.toOrderHom u)
    else g₁.toOrderHom (a.toOrderHom u)) =
      (before K' (a.toOrderHom t) ≫
        path K' B g₀ g₁ h (a.toOrderHom t)).toOrderHom (a.toOrderHom u)
  rw [before_path]
  by_cases hu : u.val ≤ t.val
  · have ha : (a.toOrderHom u).val ≤ (a.toOrderHom t).val :=
      Fin.le_iff_val_le_val.mp
        (a.toOrderHom.monotone (Fin.le_iff_val_le_val.mpr hu))
    simp [hu, ha]
  · have htu : t < u := Fin.lt_def.mpr (by omega)
    by_cases ha : (a.toOrderHom u).val ≤ (a.toOrderHom t).val
    · have hle : a.toOrderHom t ≤ a.toOrderHom u :=
        a.toOrderHom.monotone (le_of_lt htu)
      have heq : a.toOrderHom u = a.toOrderHom t :=
        le_antisymm (Fin.le_iff_val_le_val.mpr ha) hle
      simp [hu, ha, hplateau u htu heq]
    · simp [hu, ha]

/-- A collapsed left-side vertex is harmless after applying a path
when the two target rows agree there. -/
theorem after_path_plateau (K K' B : SimplexCategory) (a : K ⟶ K')
    (g₀ g₁ : K' ⟶ B)
    (h : ∀ u : Fin (K'.len + 1), g₀.toOrderHom u ≤ g₁.toOrderHom u)
    (t : Fin (K.len + 1))
    (hplateau : ∀ u : Fin (K.len + 1), u < t →
      a.toOrderHom u = a.toOrderHom t →
      g₀.toOrderHom (a.toOrderHom u) = g₁.toOrderHom (a.toOrderHom u)) :
    after K t ≫ map K K' a t ≫ path K' B g₀ g₁ h (a.toOrderHom t) =
      a ≫ after K' (a.toOrderHom t) ≫
        path K' B g₀ g₁ h (a.toOrderHom t) := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext u
  rw [map_after_path]
  change (if u.val < t.val then g₀.toOrderHom (a.toOrderHom u)
    else g₁.toOrderHom (a.toOrderHom u)) =
      (after K' (a.toOrderHom t) ≫
        path K' B g₀ g₁ h (a.toOrderHom t)).toOrderHom (a.toOrderHom u)
  rw [after_path]
  by_cases hu : u.val < t.val
  · have hlt : u < t := Fin.lt_def.mpr hu
    by_cases ha : (a.toOrderHom u).val < (a.toOrderHom t).val
    · simp [hu, ha]
    · have hle : a.toOrderHom u ≤ a.toOrderHom t :=
        a.toOrderHom.monotone (le_of_lt hlt)
      have heq : a.toOrderHom u = a.toOrderHom t :=
        le_antisymm hle (Fin.le_iff_val_le_val.mpr (by omega))
      simp [hu, ha, hplateau u hlt heq]
  · have htu : t ≤ u := Fin.le_iff_val_le_val.mpr (by omega)
    have ha : ¬ (a.toOrderHom u).val < (a.toOrderHom t).val :=
      Nat.not_lt_of_ge (Fin.le_iff_val_le_val.mp (a.toOrderHom.monotone htu))
    simp [hu, ha]

/-- A constant ordinal operator gives a concrete failure of unrestricted
commutation with the lower embedding. -/
example : before ⦋1⦌ (0 : Fin 2) ≫
    map ⦋1⦌ ⦋0⦌ (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0) 0 ≠
      SimplexCategory.const ⦋1⦌ ⦋0⦌ 0 ≫ before ⦋0⦌ 0 := by
  decide

example : after ⦋1⦌ (1 : Fin 2) ≫
    map ⦋1⦌ ⦋0⦌ (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0) 1 ≠
      SimplexCategory.const ⦋1⦌ ⦋0⦌ 0 ≫ after ⦋0⦌ 0 := by
  decide

/-- The staircase operator of an identity ordinal map is the identity. -/
theorem map_id (K : SimplexCategory) (t : Fin (K.len + 1)) :
    map K K (𝟙 K) t = 𝟙 ⦋K.len + 1⦌ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext v
  apply (staircaseOrder_injective K.len t)
  change staircaseOrder K.len t ((map K K (𝟙 K) t).toOrderHom v) =
    staircaseOrder K.len t ((𝟙 ⦋K.len + 1⦌).toOrderHom v)
  simpa using (staircaseOrder_map K K (𝟙 K) t v)

/-- Staircase operators compose exactly with ordinal operators. -/
theorem map_comp (K K' K'' : SimplexCategory) (a : K ⟶ K') (b : K' ⟶ K'')
    (t : Fin (K.len + 1)) :
    map K K' a t ≫ map K' K'' b (a.toOrderHom t) =
      map K K'' (a ≫ b) t := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext v
  apply (staircaseOrder_injective K''.len
    (b.toOrderHom (a.toOrderHom t)))
  change staircaseOrder K''.len (b.toOrderHom (a.toOrderHom t))
      ((map K' K'' b (a.toOrderHom t)).toOrderHom
        ((map K K' a t).toOrderHom v)) =
    staircaseOrder K''.len (b.toOrderHom (a.toOrderHom t))
      ((map K K'' (a ≫ b) t).toOrderHom v)
  let p := staircaseOrder K.len t v
  have h₂ := staircaseOrder_map K K'' (a ≫ b) t v
  change staircaseOrder K''.len (b.toOrderHom (a.toOrderHom t))
      ((map K K'' (a ≫ b) t).toOrderHom v) =
    (p.1, b.toOrderHom (a.toOrderHom p.2)) at h₂
  calc
    staircaseOrder K''.len (b.toOrderHom (a.toOrderHom t))
        ((map K' K'' b (a.toOrderHom t)).toOrderHom
          ((map K K' a t).toOrderHom v)) =
      ((staircaseOrder K'.len (a.toOrderHom t)
        ((map K K' a t).toOrderHom v)).1,
        b.toOrderHom (staircaseOrder K'.len (a.toOrderHom t)
          ((map K K' a t).toOrderHom v)).2) :=
      staircaseOrder_map K' K'' b (a.toOrderHom t) _
    _ = (p.1, b.toOrderHom (a.toOrderHom p.2)) := by
      rw [staircaseOrder_map K K' a t]
    _ = staircaseOrder K''.len (b.toOrderHom (a.toOrderHom t))
        ((map K K'' (a ≫ b) t).toOrderHom v) := h₂.symm
end DaggerModels.PartII.JTOrdinalStaircaseNaturality
