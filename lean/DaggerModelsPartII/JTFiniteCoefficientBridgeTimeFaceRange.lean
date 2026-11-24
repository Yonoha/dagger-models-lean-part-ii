import DaggerModelsPartII.JTFiniteCoefficientBridgeCopyFace

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open MonoidalCategory CartesianMonoidalCategory
open scoped SSet.modelCategoryQuillen

universe v

namespace DaggerModels.PartII.JTFiniteCoefficientBridgeCopyFace

open JTFiniteCoefficientBridgeTime (time timeVertexEquiv mapCopies_vertex)
open JTFiniteCoefficientBridgeSubcollection
open SSet.Subcomplex

noncomputable section

private abbrev simplex (a : SimplexCategory) := SSet.stdSimplex.{v}.obj a

variable {m : ℕ} {k b' : SimplexCategory}
variable {b : Fin (m + 1) → SimplexCategory}
variable (c : ∀ e, k ⟶ b e) (u : k ⟶ b') (n : SimplexCategory)

theorem timeRange_iff (S : Finset (Fin (m + 1))) (hS : S.Nonempty)
    (z : Fin ((time m n).len + 1)) :
    z ∈ Set.range (timeOperator n (copyInclusion S hS)
      (JTHigherInterleavedParameter.timeInclusion_injective S hS)).toOrderHom ↔
      ((timeVertexEquiv m n).symm z).1 ∈ S := by
  obtain ⟨x, rfl⟩ := (timeVertexEquiv m n).surjective z
  rw [Equiv.symm_apply_apply]
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨y, rfl⟩ :=
      (timeVertexEquiv (S.card - 1) n).surjective w
    rw [timeOperator, mapCopies_vertex] at hw
    have he := congrArg Prod.fst ((timeVertexEquiv m n).injective hw)
    have hy : (copyInclusion S hS).toOrderHom y.1 ∈ S := by
      simpa only [JTHigherInterleavedParameter.timeInclusion_range, Finset.mem_coe]
        using (show (copyInclusion S hS).toOrderHom y.1 ∈
          Set.range (copyInclusion S hS).toOrderHom from ⟨y.1, rfl⟩)
    exact he ▸ hy
  · intro hx
    have hrange : x.1 ∈ Set.range (copyInclusion S hS).toOrderHom := by
      rw [JTHigherInterleavedParameter.timeInclusion_range S hS]
      exact hx
    obtain ⟨e, he⟩ := hrange
    refine ⟨timeVertexEquiv (S.card - 1) n (e, x.2), ?_⟩
    rw [timeOperator, mapCopies_vertex]
    change timeVertexEquiv m n ((copyInclusion S hS).toOrderHom e, x.2) =
      timeVertexEquiv m n (x.1, x.2)
    rw [he]

theorem timeFace_eq_range (S : Finset (Fin (m + 1))) (hS : S.Nonempty) :
    timeFace.{v} (m := m) n S =
      range (SSet.stdSimplex.map
        (timeOperator n (copyInclusion S hS)
          (JTHigherInterleavedParameter.timeInclusion_injective S hS))) := by
  ext q z
  cases q using Opposite.rec with
  | op q =>
    cases q using SimplexCategory.rec with
    | _ d =>
      rw [mem_timeFace_iff]
      rw [JTFiniteCoefficientBridgeOverlap.range_stdMap_iff _
        (timeOperator_injective n (copyInclusion S hS)
          (JTHigherInterleavedParameter.timeInclusion_injective S hS))]
      simp only [timeRange_iff (m := m) n S hS]
      rfl

end
end DaggerModels.PartII.JTFiniteCoefficientBridgeCopyFace
