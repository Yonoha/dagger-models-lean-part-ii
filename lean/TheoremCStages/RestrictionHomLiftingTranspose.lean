import DaggerModelsPartII.DiagramHomPrecompLifting

/-!
# The full restriction--Hom lifting correspondence

The existing restriction/Hom equivalence supplies the reverse implication
of the checked coefficient lifting theorem. This keeps the original test
map, coefficient map, and simplicial diagram, and uses no model structure.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Simplicial

universe v u

namespace DaggerModels.PartII.RestrictionHomLiftingTranspose

noncomputable section

variable {C : Type u} [Category.{v} C] [HasLimitsOfSize.{0, v} C]

/-- Lifting against the literal Hom restriction yields lifting against the
literal limit restriction in the coefficient category. -/
theorem lifting_of_hom {K L : SSet.{v}} (j : K ⟶ L)
    {A B : C} (i : A ⟶ B) (W : SimplexCategoryᵒᵖ ⥤ C)
    (h : HasLiftingProperty j (diagramHomPrecomp i W)) :
    HasLiftingProperty i (diagramRestrictionPre j W) := by
  constructor
  intro a b sq
  let eKA := diagramRestrictionHomEquiv K A W
  let eKB := diagramRestrictionHomEquiv K B W
  let eLA := diagramRestrictionHomEquiv L A W
  let eLB := diagramRestrictionHomEquiv L B W
  let a' := eLA.symm a
  let b' := eKB.symm b
  have comm : b' ≫ diagramHomPrecomp i W = j ≫ a' := by
    apply eKA.injective
    rw [diagramRestrictionHomEquiv_coeff, diagramRestrictionHomEquiv_pre]
    change i ≫ eKB (eKB.symm b) = eLA (eLA.symm a) ≫ diagramRestrictionPre j W
    rw [eKB.apply_symm_apply, eLA.apply_symm_apply]
    exact sq.w.symm
  haveI := h
  have sq' : CommSq b' j (diagramHomPrecomp i W) a' := ⟨comm⟩
  refine CommSq.HasLift.mk' ⟨eLB sq'.lift, ?_, ?_⟩
  · rw [← diagramRestrictionHomEquiv_coeff, sq'.fac_right]
    exact eLA.apply_symm_apply a
  · rw [← diagramRestrictionHomEquiv_pre, sq'.fac_left]
    exact eKB.apply_symm_apply b

/-- The exact two lifting problems are equivalent, without a fibrancy or
model-category assumption. -/
theorem lifting_iff {K L : SSet.{v}} (j : K ⟶ L)
    {A B : C} (i : A ⟶ B) (W : SimplexCategoryᵒᵖ ⥤ C) :
    HasLiftingProperty i (diagramRestrictionPre j W) ↔
      HasLiftingProperty j (diagramHomPrecomp i W) :=
  ⟨diagramHomPrecomp_lifting_of_restriction j i W, lifting_of_hom j i W⟩

#print axioms lifting_of_hom
#print axioms lifting_iff

end
end DaggerModels.PartII.RestrictionHomLiftingTranspose
