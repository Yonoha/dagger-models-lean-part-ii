import DaggerModelsPartII.ReedyExtendTransformation

/-! The lower degrees with one additional top simplex, and its image factorizations. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII

/-- Interpret the added point as `[n]` in the opposite simplex category. -/
def extensionIndexObj (n : ℕ) : Option (BelowDegree n) → SimplexCategoryᵒᵖ
  | none => op ⦋n⦌
  | some s => s.obj

abbrev ExtensionIndex (n : ℕ) := InducedCategory SimplexCategoryᵒᵖ (extensionIndexObj n)

def extensionIndexTop (n : ℕ) : ExtensionIndex n := none

def extensionIndexLower {n : ℕ} (s : BelowDegree n) : ExtensionIndex n := some s

theorem extensionIndexObj_injective (n : ℕ) : Function.Injective (extensionIndexObj n) := by
  intro s t h
  cases s with
  | none =>
    cases t with
    | none => rfl
    | some t =>
      have h' : op ⦋n⦌ = t.obj := h
      have ht := t.property
      change t.obj.unop.len < n at ht
      rw [← h'] at ht
      exact (Nat.lt_irrefl n ht).elim
  | some s =>
    cases t with
    | none =>
      have h' : s.obj = op ⦋n⦌ := h
      have hs := s.property
      change s.obj.unop.len < n at hs
      rw [h'] at hs
      exact (Nat.lt_irrefl n hs).elim
    | some t =>
      exact congrArg some (ObjectProperty.FullSubcategory.ext h)

theorem extensionIndexObj_degree_le {n : ℕ} (s : ExtensionIndex n) :
    (extensionIndexObj n s).unop.len ≤ n := by
  cases s with
  | none => exact Nat.le_refl _
  | some s => exact Nat.le_of_lt s.property

/-- Realize an opposite simplex of degree at most `n` as an extension index. -/
def extensionIndexOfDegree (n : ℕ) (s : SimplexCategoryᵒᵖ) : ExtensionIndex n :=
  if h : s.unop.len < n then some ⟨s, h⟩ else none

theorem extensionIndexOfDegree_obj {n : ℕ} {s : SimplexCategoryᵒᵖ}
    (hs : s.unop.len ≤ n) : extensionIndexObj n (extensionIndexOfDegree n s) = s := by
  by_cases h : s.unop.len < n
  · simp only [extensionIndexOfDegree, dif_pos h, extensionIndexObj]
  · rw [extensionIndexOfDegree, dif_neg h]
    exact congrArg op (SimplexCategory.ext _ _ (by
      change n = s.unop.len
      omega))

/-- An inverse/direct decomposition internal to the one-degree extension. -/
structure ExtensionIndexFactor {n : ℕ} {s t : ExtensionIndex n} (f : s ⟶ t) where
  mid : ExtensionIndex n
  inverse : s ⟶ mid
  direct : mid ⟶ t
  inverse_mono : Mono inverse.hom.unop
  direct_epi : Epi direct.hom.unop
  fac : inverse ≫ direct = f

noncomputable section

variable {n : ℕ} {s t : ExtensionIndex n}

def extensionIndexFactor (f : s ⟶ t) : ExtensionIndexFactor f := by
  let m := extensionIndexOfDegree n (simplexReedyMid f.hom)
  have hm : extensionIndexObj n m = simplexReedyMid f.hom :=
    extensionIndexOfDegree_obj ((simplexReedyMid_le_source f.hom).trans
      (extensionIndexObj_degree_le s))
  refine ⟨m, ⟨simplexReedyInverse f.hom ≫ eqToHom hm.symm⟩,
    ⟨eqToHom hm ≫ simplexReedyDirect f.hom⟩, ?_, ?_, ?_⟩
  · change Mono (simplexReedyInverse f.hom ≫ eqToHom hm.symm).unop
    rw [unop_comp]
    infer_instance
  · change Epi (eqToHom hm ≫ simplexReedyDirect f.hom).unop
    rw [unop_comp]
    infer_instance
  · apply InducedCategory.hom_ext
    change (simplexReedyInverse f.hom ≫ eqToHom hm.symm) ≫
      (eqToHom hm ≫ simplexReedyDirect f.hom) = f.hom
    simp

theorem ExtensionIndexFactor.mid_eq {f : s ⟶ t} (F G : ExtensionIndexFactor f) :
    F.mid = G.mid := by
  letI := F.inverse_mono
  letI := F.direct_epi
  letI := G.inverse_mono
  letI := G.direct_epi
  exact extensionIndexObj_injective n
    ((simplexReedyMid_eq_of_factor (congrArg InducedCategory.Hom.hom F.fac)).symm.trans
      (simplexReedyMid_eq_of_factor (congrArg InducedCategory.Hom.hom G.fac)))

instance (f : s ⟶ t) : Subsingleton (ExtensionIndexFactor f) where
  allEq F G := by
    have h := F.mid_eq G
    cases F with
    | mk m l r hl hr hf =>
      cases G with
      | mk m' l' r' hl' hr' hf' =>
        change m = m' at h
        subst m'
        letI := hl
        letI := hr
        letI := hl'
        letI := hr'
        have h₁ := simplexReedyFactor_compare (congrArg InducedCategory.Hom.hom hf)
        have h₂ := simplexReedyFactor_compare (congrArg InducedCategory.Hom.hom hf')
        have he₁ : l = l' := InducedCategory.hom_ext (h₁.1.symm.trans h₂.1)
        have he₂ : r = r' := by
          apply InducedCategory.hom_ext
          have e := h₁.2.trans h₂.2.symm
          exact (cancel_epi (eqToHom (simplexReedyMid_eq_of_factor
            (congrArg InducedCategory.Hom.hom hf)))).mp e
        subst l'
        subst r'
        rfl

end

end DaggerModels.PartII
