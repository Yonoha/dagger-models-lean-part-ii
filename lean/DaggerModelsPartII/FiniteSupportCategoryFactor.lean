import DaggerModelsPartII.NerveVertexSupport
import DaggerModelsPartII.FiniteLastVertexSupport

/-! On any finite simplicial support it suffices to compare the exact evaluation
on the full category spanned by the support's vertices. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerNerveHomotopy
open scoped SSet.modelCategoryQuillen
open DaggerSSetGluing DaggerOriginalProductGadget

namespace DaggerModels.PartII.FiniteLastVertexSupport

noncomputable section

variable {C D : Type} [SmallCategory C] [SmallCategory D] (e : D ⥤ C)

/-- It suffices to provide the contractible comparison on a weak cover of
each finite-object full subcategory. -/
theorem of_finite_full_weak_cover_factors
    (h : ∀ (P : ObjectProperty D), Finite P.FullSubcategory →
      ∃ (B E : Cat.{0, 0}) (p : B ⥤ P.FullSubcategory) (F : B ⥤ E) (G : E ⥤ C),
        WeakEquivalence (nerveMap p) ∧ GW (pointMap (nerve E)) ∧
          NatTransZigzag (p ⋙ P.ι ⋙ e) (F ⋙ G)) :
    SupportNullhomotopies e := by
  intro S hS
  let P := NerveVertexSupport.present S
  let l := NerveVertexSupport.lift S
  obtain ⟨B, E, p, F, G, hp, hE, hz⟩ := h P (NerveVertexSupport.finite_objects S hS)
  letI := hp
  obtain ⟨v, ⟨H⟩⟩ := FiniteLastVertexFactor.nerveMap_nullhomotopic_of_weak_cover
    p (P.ι ⋙ e) F G hE hz
  have heval : l ≫ nerveMap (P.ι ⋙ e) = S.ι ≫ nerveMap e := by rfl
  let q := SSet.stdSimplex.isTerminalObj₀.from (nerve P.FullSubcategory)
  have hpoint : l ≫ q = SSet.stdSimplex.isTerminalObj₀.from S.toSSet :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  refine ⟨v, ⟨(H.precomp (R.map l)).congr ?_ ?_⟩⟩
  · rw [← R.map_comp, heval]
  · rw [← R.map_comp, ← Category.assoc, hpoint]

/-- A weakly contractible factor of the evaluation on each finite-object
full subcategory provides the required nullhomotopies on finite supports. -/
theorem of_finite_full_factors
    (h : ∀ (P : ObjectProperty D), Finite P.FullSubcategory →
      ∃ (E : Cat.{0, 0}) (F : P.FullSubcategory ⥤ E) (G : E ⥤ C),
        GW (pointMap (nerve E)) ∧ NatTransZigzag (P.ι ⋙ e) (F ⋙ G)) :
    SupportNullhomotopies e := by
  apply of_finite_full_weak_cover_factors
  intro P hP
  obtain ⟨E, F, G, hE, hz⟩ := h P hP
  have hi : WeakEquivalence (nerveMap (𝟭 P.FullSubcategory)) := by
    have hid : nerveMap (𝟭 P.FullSubcategory) = 𝟙 (nerve P.FullSubcategory) :=
      nerveFunctor.map_id (Cat.of P.FullSubcategory)
    rw [hid]
    infer_instance
  exact ⟨Cat.of P.FullSubcategory, E, 𝟭 _, F, G, hi, hE, hz⟩

end
end DaggerModels.PartII.FiniteLastVertexSupport
