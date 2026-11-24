import DaggerModelsPartII.DiagramRestriction
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-! Restrictions on standard simplices and pushouts of simplicial sets. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe v u

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C] [HasLimitsOfSize.{0, v} C]
  (W : SimplexCategoryᵒᵖ ⥤ C)

private def simplexIdentity (n : ℕ) : (Δ[n] : SSet.{v}).Elements :=
  ⟨op ⦋n⦌, SSet.stdSimplex.objEquiv.symm (𝟙 _)⟩

private def simplexIdentityIsInitial (n : ℕ) : IsInitial (simplexIdentity.{v} n) :=
  IsInitial.ofUniqueHom
    (fun d ↦ ⟨(SSet.stdSimplex.objEquiv d.2).op, by
      change SSet.stdSimplex.objEquiv.symm (SSet.stdSimplex.objEquiv d.2 ≫ 𝟙 _) = d.2
      rw [Category.comp_id, Equiv.symm_apply_apply]⟩)
    (fun d g ↦ by
      apply Subtype.ext
      apply Quiver.Hom.unop_inj
      have h := g.property
      change SSet.stdSimplex.objEquiv.symm (g.val.unop ≫ 𝟙 _) = d.2 at h
      rw [Category.comp_id] at h
      exact SSet.stdSimplex.objEquiv.symm_apply_eq.mp h)

/-- Restriction to the standard simplex is evaluation in its degree. -/
def diagramRestrictionSimplexIso (n : ℕ) :
    diagramRestriction (Δ[n] : SSet.{v}) W ≅ W.obj (op ⦋n⦌) :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _)
    (limitOfDiagramInitial (simplexIdentityIsInitial n) _)

theorem diagramRestrictionSimplexIso_hom (n : ℕ) :
    (diagramRestrictionSimplexIso W n).hom =
      limit.π (CategoryOfElements.π (Δ[n] : SSet.{v}) ⋙ W) (simplexIdentity n) :=
  rfl

/-- The simplex comparison is natural in the simplex operator. -/
theorem diagramRestrictionSimplexIso_natural {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) :
    diagramRestrictionPre (SSet.stdSimplex.map f) W ≫ (diagramRestrictionSimplexIso W m).hom =
      (diagramRestrictionSimplexIso W n).hom ≫ W.map f.op := by
  rw [diagramRestrictionSimplexIso_hom, diagramRestrictionSimplexIso_hom, diagramRestrictionPre_π]
  let d := (CategoryOfElements.map (SSet.stdSimplex.map f)).obj (simplexIdentity m)
  let e : simplexIdentity.{v} n ⟶ d := ⟨f.op, by
    change SSet.stdSimplex.objEquiv.symm (f ≫ 𝟙 _) =
      SSet.stdSimplex.objEquiv.symm (𝟙 _ ≫ f)
    rw [Category.comp_id, Category.id_comp]⟩
  exact (limit.w (CategoryOfElements.π (Δ[n] : SSet.{v}) ⋙ W) e).symm

/-- Restriction sends a pushout in the test simplicial set to a pullback. -/
theorem diagramRestriction_isPullback {K L M N : SSet.{v}} {f : K ⟶ L} {g : K ⟶ M}
    {i : L ⟶ N} {j : M ⟶ N} (sq : IsPushout f g i j) :
    IsPullback (diagramRestrictionPre i W) (diagramRestrictionPre j W)
      (diagramRestrictionPre f W) (diagramRestrictionPre g W) := by
  letI := (diagramRestrictionAdjunction W).rightAdjoint_preservesLimits
  exact (sq.op.map (diagramRestrictionFunctor W)).flip

end

end DaggerModels.PartII
