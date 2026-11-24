import DaggerModelsPartII.ReedyMatchingLifting
import DaggerModelsPartII.ReedyLatchingLifting
import DaggerModelsPartII.ReedyTrivialRecognition
import Mathlib.AlgebraicTopology.ModelCategory.Basic

/-! The Reedy model structure on simplicial objects with model-category coefficients. -/

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Opposite

universe v u

namespace DaggerModels.PartII

variable (C : Type u) [Category.{v} C] [ModelCategory C]

/-- Levelwise weak equivalences for simplicial objects. -/
def simplicialReedyWeakEquivalences : MorphismProperty (SimplexCategoryᵒᵖ ⥤ C) :=
  (weakEquivalences C).functorCategory SimplexCategoryᵒᵖ

instance simplicialReedyWeakEquivalences_hasTwoOutOfThree :
    (simplicialReedyWeakEquivalences C).HasTwoOutOfThreeProperty where
  comp_mem f g hf hg := fun n ↦ (weakEquivalences C).comp_mem
    (f.app n) (g.app n) (hf n) (hg n)
  of_precomp f g hf hfg := fun n ↦ (weakEquivalences C).of_precomp
    (f.app n) (g.app n) (hf n) (hfg n)
  of_postcomp f g hg hfg := fun n ↦ (weakEquivalences C).of_postcomp
    (f.app n) (g.app n) (hg n) (hfg n)

variable [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]

omit [HasColimitsOfSize.{0, 0} C] in
/-- Relative trivial matching maps characterize the levelwise weak Reedy fibrations. -/
theorem simplicialReedyFibrations_inf_weakEquivalences :
    reedyMatchingProperty (fibrations C) ⊓ simplicialReedyWeakEquivalences C =
      reedyMatchingProperty (trivialFibrations C) := by
  letI : (fibrations C ⊓ weakEquivalences C).IsStableUnderBaseChange := by
    change (trivialFibrations C).IsStableUnderBaseChange
    rw [← rlp_eq_of_wfs (cofibrations C) (trivialFibrations C)]
    infer_instance
  ext X Y f
  apply reedyMatching_inf_levelwise_eq
    (f := f) (fibrations C) (weakEquivalences C)
  intro n hf
  change trivialFibrations C ((matchingFunctor n).map f)
  rw [← rlp_eq_of_wfs (cofibrations C) (trivialFibrations C)]
  apply matchingFunctor_map_rlp
  intro m hm
  rw [rlp_eq_of_wfs (cofibrations C) (trivialFibrations C)]
  exact hf m hm

omit [HasLimitsOfSize.{0, 0} C] in
/-- Relative trivial latching maps characterize the levelwise weak Reedy cofibrations. -/
theorem simplicialReedyCofibrations_inf_weakEquivalences :
    reedyLatchingProperty (cofibrations C) ⊓ simplicialReedyWeakEquivalences C =
      reedyLatchingProperty (trivialCofibrations C) := by
  letI : IsStableUnderCobaseChange (cofibrations C ⊓ weakEquivalences C) := by
    change (trivialCofibrations C).IsStableUnderCobaseChange
    rw [← llp_eq_of_wfs (trivialCofibrations C) (fibrations C)]
    infer_instance
  ext X Y f
  apply reedyLatching_inf_levelwise_eq
    (f := f) (cofibrations C) (weakEquivalences C)
  intro n hf
  change trivialCofibrations C ((latchingFunctor n).map f)
  rw [← llp_eq_of_wfs (trivialCofibrations C) (fibrations C)]
  apply latchingFunctor_map_llp
  intro m hm
  rw [llp_eq_of_wfs (trivialCofibrations C) (fibrations C)]
  exact hf m hm

/-- The Reedy model structure for simplicial objects in a model category. -/
noncomputable def simplicialReedyModelCategory : ModelCategory (SimplexCategoryᵒᵖ ⥤ C) := by
  let D := SimplexCategoryᵒᵖ ⥤ C
  let I := reedyLatchingProperty (cofibrations C)
  let P := reedyMatchingProperty (fibrations C)
  let W := simplicialReedyWeakEquivalences C
  letI : CategoryWithCofibrations D := ⟨I⟩
  letI : CategoryWithFibrations D := ⟨P⟩
  letI : CategoryWithWeakEquivalences D := ⟨W⟩
  letI : (weakEquivalences D).HasTwoOutOfThreeProperty :=
    simplicialReedyWeakEquivalences_hasTwoOutOfThree C
  letI : IsWeakFactorizationSystem (cofibrations D) (trivialFibrations D) := by
    change IsWeakFactorizationSystem I (reedyMatchingProperty (fibrations C) ⊓
      simplicialReedyWeakEquivalences C)
    rw [simplicialReedyFibrations_inf_weakEquivalences C]
    exact reedyRelativeWeakFactorizationSystem (cofibrations C) (trivialFibrations C)
  letI : IsWeakFactorizationSystem (trivialCofibrations D) (fibrations D) := by
    change IsWeakFactorizationSystem (reedyLatchingProperty (cofibrations C) ⊓
      simplicialReedyWeakEquivalences C) P
    rw [simplicialReedyCofibrations_inf_weakEquivalences C]
    exact reedyRelativeWeakFactorizationSystem (trivialCofibrations C) (fibrations C)
  exact ModelCategory.mk' _

end DaggerModels.PartII
