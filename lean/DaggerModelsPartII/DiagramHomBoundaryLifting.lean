import DaggerModelsPartII.BoundaryDiagramHom
import Mathlib.CategoryTheory.LiftingProperties.Basic

/-! Boundary lifting for levelwise Hom simplicial sets. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe v u

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C] [HasLimitsOfSize.{0, 0} C]

/-- Precomposition has boundary lifting when the coefficient map lifts against matching. -/
theorem diagramHomPrecomp_boundary_lifting (n : ℕ) {A B : C} (i : A ⟶ B)
    (W : SimplexCategoryᵒᵖ ⥤ C) (h : HasLiftingProperty i ((matchingComparison n).app W)) :
    HasLiftingProperty (SSet.boundary.{v} n).ι (diagramHomPrecomp i W) := by
  constructor
  intro a b sq
  let a' : B ⟶ (matchingFunctor n).obj W := boundaryDiagramHomEquiv n B W a
  let b' : A ⟶ W.obj (op ⦋n⦌) := SSet.yonedaEquiv b
  have sq' : CommSq b' i ((matchingComparison n).app W) a' := by
    constructor
    change SSet.yonedaEquiv b ≫ (matchingComparison n).app W =
      i ≫ boundaryDiagramHomEquiv n B W a
    rw [← boundaryDiagramHomEquiv_restrict, ← boundaryDiagramHomEquiv_precomp, sq.w]
  letI := h
  refine CommSq.HasLift.mk' ⟨SSet.yonedaEquiv.symm sq'.lift, ?_, ?_⟩
  · apply (boundaryDiagramHomEquiv n B W).injective
    rw [boundaryDiagramHomEquiv_restrict, Equiv.apply_symm_apply]
    exact sq'.fac_right
  · apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact sq'.fac_left

/-- Postcomposition has boundary lifting from lifting against relative matching maps. -/
theorem diagramHomPostcomp_boundary_lifting [HasInitial C] (n : ℕ) (A : C)
    {W V : SimplexCategoryᵒᵖ ⥤ C} (f : W ⟶ V)
    (h : HasLiftingProperty (initial.to A) (relativeMatchingMap n f)) :
    HasLiftingProperty (SSet.boundary.{v} n).ι (diagramHomPostcomp A f) := by
  constructor
  intro a b sq
  let a' : A ⟶ (matchingFunctor n).obj W := boundaryDiagramHomEquiv n A W a
  let b' : A ⟶ V.obj (op ⦋n⦌) := SSet.yonedaEquiv b
  have hc : a' ≫ (matchingFunctor n).map f = b' ≫ (matchingComparison n).app V := by
    change boundaryDiagramHomEquiv n A W a ≫ (matchingFunctor n).map f =
      SSet.yonedaEquiv b ≫ (matchingComparison n).app V
    rw [← boundaryDiagramHomEquiv_postcomp, ← boundaryDiagramHomEquiv_restrict, sq.w]
  let b'' := pullback.lift a' b' hc
  have sq' : CommSq (initial.to _) (initial.to A) (relativeMatchingMap n f) b'' :=
    ⟨initialIsInitial.hom_ext _ _⟩
  letI := h
  have hf := sq'.fac_right
  refine CommSq.HasLift.mk' ⟨SSet.yonedaEquiv.symm sq'.lift, ?_, ?_⟩
  · apply (boundaryDiagramHomEquiv n A W).injective
    rw [boundaryDiagramHomEquiv_restrict, Equiv.apply_symm_apply]
    have hh : (sq'.lift ≫ relativeMatchingMap n f) ≫ pullback.fst _ _ =
        b'' ≫ pullback.fst _ _ := by rw [hf]
    simpa only [Category.assoc, relativeMatchingMap, b'', pullback.lift_fst] using hh
  · apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    have hh : (sq'.lift ≫ relativeMatchingMap n f) ≫ pullback.snd _ _ =
        b'' ≫ pullback.snd _ _ := by rw [hf]
    simpa only [Category.assoc, relativeMatchingMap, b'', pullback.lift_snd] using hh

end

end DaggerModels.PartII
