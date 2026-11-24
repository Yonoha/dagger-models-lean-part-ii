import ChosenNecklaceIntersections

/-! A vertex of a necklace is incident to at most two positive maximal beads. -/

set_option autoImplicit false
set_option warningAsError true

open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTIncidentBeadCombinatorics

variable {T : NecklaceCode}

/-- Incidence uses the full interval of the original positive maximal bead. -/
def Incident (v : Fin (T.len + 1)) (B : T.Bead) : Prop := v ∈ B.interval

/-- A positive maximal bead is determined by its right endpoint as well as its left endpoint. -/
theorem bead_right_injective (B C : T.Bead) (h : B.right = C.right) : B = C := by
  by_contra hne
  have hv : B.right ∈ B.interval ∩ C.interval :=
    Finset.mem_inter.mpr ⟨B.right_mem_interval, h ▸ C.right_mem_interval⟩
  rcases (B.mem_inter_iff C hne B.right).mp hv with ⟨ha, _⟩ | ⟨ha, _⟩
  · exact (ne_of_lt C.lt) (ha.symm.trans h)
  · exact (ne_of_lt B.lt) (ha.symm.trans h.symm)

private theorem cover_adjacent {v : Fin (T.len + 1)} (B₀ B₁ : T.Bead)
    (ha : B₀.right = B₁.left) (hv : v = B₀.right)
    (B : T.Bead) (hB : Incident v B) : B = B₀ ∨ B = B₁ := by
  by_cases h₀ : B = B₀
  · exact Or.inl h₀
  have hi : v ∈ B₀.interval ∩ B.interval :=
    Finset.mem_inter.mpr ⟨hv ▸ B₀.right_mem_interval, hB⟩
  rcases (B₀.mem_inter_iff B (Ne.symm h₀) v).mp hi with ⟨he, _⟩ | ⟨he, hvB⟩
  · exact Or.inr (B.left_injective B₁ (he.symm.trans ha))
  · have hh : B₀.right = B₀.left := hv.symm.trans (hvB.trans he)
    exact False.elim ((ne_of_lt B₀.lt) hh.symm)

/-- Two distinct incident positive maximal beads cover every bead incident to the same vertex. -/
theorem incident_cover_of_distinct {v : Fin (T.len + 1)} (B₀ B₁ : T.Bead)
    (hne : B₀ ≠ B₁) (h₀ : Incident v B₀) (h₁ : Incident v B₁)
    (B : T.Bead) (hB : Incident v B) : B = B₀ ∨ B = B₁ := by
  have hi : v ∈ B₀.interval ∩ B₁.interval := Finset.mem_inter.mpr ⟨h₀, h₁⟩
  rcases (B₀.mem_inter_iff B₁ hne v).mp hi with ⟨ha, hv⟩ | ⟨ha, hv⟩
  · exact cover_adjacent B₀ B₁ ha hv B hB
  · exact (cover_adjacent B₁ B₀ ha hv B hB).symm

/-- Among three incident positive maximal beads, two are equal. -/
theorem incident_three_eq {v : Fin (T.len + 1)} (B₀ B₁ B₂ : T.Bead)
    (h₀ : Incident v B₀) (h₁ : Incident v B₁) (h₂ : Incident v B₂) :
    B₀ = B₁ ∨ B₀ = B₂ ∨ B₁ = B₂ := by
  by_cases h : B₀ = B₁
  · exact Or.inl h
  rcases incident_cover_of_distinct B₀ B₁ h h₀ h₁ B₂ h₂ with h₂₀ | h₂₁
  · exact Or.inr (Or.inl h₂₀.symm)
  · exact Or.inr (Or.inr h₂₁.symm)

/-- Exact zero, one, or two cases, with incident witnesses and no omitted empty case. -/
theorem incident_cases (T : NecklaceCode) (v : Fin (T.len + 1)) :
    (∀ B : T.Bead, ¬ Incident v B) ∨
      (∃ B₀ : T.Bead, Incident v B₀ ∧ ∀ B, Incident v B → B = B₀) ∨
      (∃ B₀ B₁ : T.Bead, B₀ ≠ B₁ ∧ Incident v B₀ ∧ Incident v B₁ ∧
        ∀ B, Incident v B → B = B₀ ∨ B = B₁) := by
  classical
  by_cases h : ∃ B : T.Bead, Incident v B
  · obtain ⟨B₀, h₀⟩ := h
    by_cases h' : ∃ B₁ : T.Bead, Incident v B₁ ∧ B₁ ≠ B₀
    · obtain ⟨B₁, h₁, hne⟩ := h'
      exact Or.inr (Or.inr ⟨B₀, B₁, Ne.symm hne, h₀, h₁,
        incident_cover_of_distinct B₀ B₁ (Ne.symm hne) h₀ h₁⟩)
    · refine Or.inr (Or.inl ⟨B₀, h₀, ?_⟩)
      intro B hB
      by_contra hne
      exact h' ⟨B, hB, hne⟩
  · exact Or.inl (fun B hB ↦ h ⟨B, hB⟩)

end DaggerModels.PartII.JTIncidentBeadCombinatorics
