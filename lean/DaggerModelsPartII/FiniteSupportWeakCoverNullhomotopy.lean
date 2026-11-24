import DaggerModelsPartII.FiniteSupportCategoryFactor

/-! Descend covered evaluation nullhomotopies without a contractible category factor. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Simplicial HomotopicalAlgebra DaggerNerveHomotopy
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.FiniteLastVertexSupport

noncomputable section

private abbrev toPoint (X : SSet.{0}) := SSet.stdSimplex.isTerminalObj₀.from X

/-- A nullhomotopy of a covered evaluation descends across a weak cover and
an actual natural-transformation zigzag in the same target category. -/
theorem nullhomotopic_of_weak_cover {C D B : Type}
    [SmallCategory C] [SmallCategory D] [SmallCategory B]
    (p : D ⥤ B) [WeakEquivalence (nerveMap p)]
    (L : B ⥤ C) (E : D ⥤ C) (h : NatTransZigzag (p ⋙ L) E)
    (v : (Δ[0] : SSet.{0}) ⟶ nerve C)
    (H : SSet.Homotopy (R.map (nerveMap E)) (R.map (toPoint (nerve D) ≫ v))) :
    Nonempty (SSet.Homotopy (R.map (nerveMap L))
      (R.map (toPoint (nerve B) ≫ v))) := by
  letI : WeakEquivalence (R.map (nerveMap p)) := FiniteWeakCover.weak_singular _
  have hp : nerveMap p ≫ toPoint (nerve B) = toPoint (nerve D) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  refine ⟨FiniteWeakCover.homotopyOfPrecomp (R.map (nerveMap p)) ?_⟩
  have K := (zigzagHomotopy h).some.trans H
  rw [← R.map_comp, ← R.map_comp, ← Category.assoc, hp]
  exact K

/-- Nullhomotopies on weak covers of the finite-object full subcategories
give nullhomotopies on every finite simplicial support of the original evaluation. -/
theorem of_finite_full_weak_cover_nullhomotopies
    {C D : Type} [SmallCategory C] [SmallCategory D] (e : D ⥤ C)
    (h : ∀ (P : ObjectProperty D), Finite P.FullSubcategory →
      ∃ (B : Cat.{0, 0}) (p : B ⥤ P.FullSubcategory) (E : B ⥤ C),
        WeakEquivalence (nerveMap p) ∧ NatTransZigzag (p ⋙ P.ι ⋙ e) E ∧
          ∃ v : (Δ[0] : SSet.{0}) ⟶ nerve C,
            Nonempty (SSet.Homotopy (R.map (nerveMap E))
              (R.map (toPoint (nerve B) ≫ v)))) :
    SupportNullhomotopies e := by
  intro S hS
  let P := NerveVertexSupport.present S
  let l := NerveVertexSupport.lift S
  obtain ⟨B, p, E, hp, hz, v, ⟨H⟩⟩ := h P (NerveVertexSupport.finite_objects S hS)
  letI := hp
  obtain ⟨K⟩ := nullhomotopic_of_weak_cover p (P.ι ⋙ e) E hz v H
  have heval : l ≫ nerveMap (P.ι ⋙ e) = S.ι ≫ nerveMap e := by rfl
  have hpoint : l ≫ toPoint (nerve P.FullSubcategory) = toPoint S.toSSet :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  refine ⟨v, ⟨(K.precomp (R.map l)).congr ?_ ?_⟩⟩
  · rw [← R.map_comp, heval]
  · rw [← R.map_comp, ← Category.assoc, hpoint]

end

end DaggerModels.PartII.FiniteLastVertexSupport
