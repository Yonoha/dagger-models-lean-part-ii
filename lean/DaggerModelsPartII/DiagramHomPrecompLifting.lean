import DaggerModelsPartII.DiagramRestriction
import DaggerModelsPartII.DiagramHomBoundaryLifting
import DaggerModelsPartII.ReedyHornRestriction
import TopCatModelCategory.ModelCategorySSet
import Mathlib.CategoryTheory.LiftingProperties.Basic

/-!
# Coefficient lifting implies mapping-space precomposition lifting

The restriction--Hom equivalence turns a lifting problem for a map of
simplicial sets into a lifting problem in the coefficient category. This
statement needs limits but no model-category structure.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Simplicial HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

universe v u

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C] [HasLimitsOfSize.{0, v} C]

/-- Lifting against a restriction map in the coefficient category gives
lifting against precomposition on the diagram Hom simplicial set. -/
theorem diagramHomPrecomp_lifting_of_restriction
    {K L : SSet.{v}} (j : K ⟶ L) {A B : C} (i : A ⟶ B)
    (W : SimplexCategoryᵒᵖ ⥤ C)
    (h : HasLiftingProperty i (diagramRestrictionPre j W)) :
    HasLiftingProperty j (diagramHomPrecomp i W) := by
  constructor
  intro a b sq
  let eK := diagramRestrictionHomEquiv K B W
  let eL := diagramRestrictionHomEquiv L A W
  let a' : B ⟶ diagramRestriction K W := eK a
  let b' : A ⟶ diagramRestriction L W := eL b
  have comm : b' ≫ diagramRestrictionPre j W = i ≫ a' := by
    calc
      b' ≫ diagramRestrictionPre j W =
          diagramRestrictionHomEquiv K A W (j ≫ b) :=
        (diagramRestrictionHomEquiv_pre j b).symm
      _ = diagramRestrictionHomEquiv K A W
            (a ≫ diagramHomPrecomp i W) :=
        congrArg (diagramRestrictionHomEquiv K A W) sq.w.symm
      _ = i ≫ a' := diagramRestrictionHomEquiv_coeff K i a
  letI := h
  have sq' : CommSq b' i (diagramRestrictionPre j W) a' := ⟨comm⟩
  let eLB := diagramRestrictionHomEquiv L B W
  refine CommSq.HasLift.mk' ⟨eLB.symm sq'.lift, ?_, ?_⟩
  · apply eK.injective
    rw [diagramRestrictionHomEquiv_pre, Equiv.apply_symm_apply]
    exact sq'.fac_right
  · apply eL.injective
    rw [diagramRestrictionHomEquiv_coeff, Equiv.apply_symm_apply]
    exact sq'.fac_left

variable [ModelCategory C] [HasLimitsOfSize.{0, 0} C]
  [HasColimitsOfSize.{0, 0} C]

local instance : ModelCategory (SimplexCategoryᵒᵖ ⥤ C) :=
  simplicialReedyModelCategory C

/-- A homotopically constant Reedy fibrant diagram sends any coefficient
cofibration by precomposition to a Kan fibration. -/
theorem diagramHomPrecomp_kanFibration
    (W : SimplexCategoryᵒᵖ ⥤ C) [IsFibrant W]
    (hW : ∀ {s t : SimplexCategoryᵒᵖ} (g : s ⟶ t),
      weakEquivalences C (W.map g))
    {A B : C} (i : A ⟶ B) (hi : cofibrations C i) :
    fibrations SSet.{v} (diagramHomPrecomp i W) := by
  rw [SSet.modelCategoryQuillen.fibrations_eq]
  intro K L j hj
  simp only [SSet.modelCategoryQuillen.J, iSup_iff] at hj
  obtain ⟨n, ⟨k⟩⟩ := hj
  exact diagramHomPrecomp_lifting_of_restriction _ _ W
    (hasLiftingProperty_of_wfs i _ hi
      (diagramRestrictionPre_horn_trivial W hW n k))

omit [HasLimitsOfSize.{0, v} C] in
/-- Reedy fibrancy alone suffices to send any coefficient trivial
cofibration by precomposition to a Kan trivial fibration. -/
theorem diagramHomPrecomp_kanTrivialFibration
    (W : SimplexCategoryᵒᵖ ⥤ C) [IsFibrant W]
    {A B : C} (i : A ⟶ B) (hi : trivialCofibrations C i) :
    trivialFibrations SSet.{v} (diagramHomPrecomp i W) := by
  rw [← SSet.modelCategoryQuillen.rlp_I_eq_trivialFibrations]
  intro X Y j hj
  obtain ⟨n⟩ := hj
  exact diagramHomPrecomp_boundary_lifting n i W
    (hasLiftingProperty_of_wfs i _ hi
      ((reedyFibrant_iff_matchingComparison W).mp inferInstance n))

end

end DaggerModels.PartII
