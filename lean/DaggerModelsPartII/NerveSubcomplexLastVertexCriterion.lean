import DaggerModelsPartII.NerveSimplexResolutionHomotopy
import DaggerModelsPartII.FiniteWeakCover
import NerveHomotopy

/-! A nullhomotopy criterion on the categories of simplices of finite subcomplexes. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerSSetGluing DaggerNerveHomotopy
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.NerveSubcomplexLastVertexCriterion

open NerveSimplexResolutionHomotopy (lastVertexOnSubcomplex comparisonOnSubcomplex)
open SimplicialResolutionFunctor (elementsProjection elementsProjection_weak)

noncomputable section

variable {C : Type} [SmallCategory C]

private abbrev toPoint (X : SSet.{0}) := SSet.stdSimplex.isTerminalObj₀.from X

/-- The last-vertex map of a subcomplex's simplex category suffices to
construct a nullhomotopy of its literal inclusion. -/
theorem inclusion_nullhomotopic (A : (nerve C).Subcomplex)
    (v : (Δ[0] : SSet.{0}) ⟶ nerve C)
    (H : SSet.Homotopy (R.map (nerveMap (lastVertexOnSubcomplex C A)))
      (R.map (toPoint (nerve A.toSSet.Elementsᵒᵖ) ≫ v))) :
    Nonempty (SSet.Homotopy (R.map A.ι) (R.map (toPoint A.toSSet ≫ v))) := by
  let a := SimplicialResolutionFunctor.augmentation.app A.toSSet
  let b := elementsProjection.app A.toSSet
  have ha : WeakEquivalence a := SimplicialResolutionFunctor.augmentation_weak _
  have hRa : WeakEquivalence (R.map a) := FiniteWeakCover.weak_singular _
  have hb : b ≫ toPoint _ = a ≫ toPoint _ :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have h₁ := (comparisonOnSubcomplex C A).toTop.toSSet
  have h₂ := H.precomp (R.map b)
  have ht : R.map b ≫ R.map (toPoint _ ≫ v) = R.map a ≫ R.map (toPoint _ ≫ v) := by
    rw [← R.map_comp, ← R.map_comp, ← Category.assoc, ← Category.assoc, hb]
  refine ⟨FiniteWeakCover.homotopyOfPrecomp (R.map a) ?_⟩
  exact (h₁.congr (R.map_comp a A.ι)
    (R.map_comp b (nerveMap (lastVertexOnSubcomplex C A)))).trans (h₂.congr rfl ht)

/-- The nerve is weakly contractible when the actual last-vertex map on
every finite subcomplex's simplex category is nullhomotopic. -/
theorem point_GW_of_last_vertex
    (h : ∀ A : (nerve C).Subcomplex, A.toSSet.IsFinite →
      ∃ v : (Δ[0] : SSet.{0}) ⟶ nerve C,
        Nonempty (SSet.Homotopy (R.map (nerveMap (lastVertexOnSubcomplex C A)))
          (R.map (toPoint (nerve A.toSSet.Elementsᵒᵖ) ≫ v)))) :
    GW (toPoint (nerve C)) := by
  apply FiniteFactorContractibility.point_GW_of_finite_nullhomotopy
  intro A hA
  obtain ⟨v, ⟨H⟩⟩ := h A hA
  exact ⟨v, inclusion_nullhomotopic A v H⟩

end
end DaggerModels.PartII.NerveSubcomplexLastVertexCriterion
