import DaggerModelsPartII.ProjectiveArrowFactorization
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# Cofibrancy of a literal arrow in the first projective Arrow WFS

The corner of the canonical map from the initial arrow to `Z` is identified
with `Z.hom` through the pushout coprojection of an isomorphism. Therefore
the actual projective cofibration condition is exactly cofibrancy of the
source together with cofibrancy of the arrow map itself.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

universe v u

namespace DaggerModels.PartII.ProjectiveArrowInitial

noncomputable section

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasColimits C]

/-- The source and target of the canonical initial arrow are initial in `C`. -/
private def initialArrow_left_isInitial :
    IsInitial (⊥_ (Arrow C)).left :=
  initialIsInitial.isInitialObj (Arrow.leftFunc : Arrow C ⥤ C)

private def initialArrow_right_isInitial :
    IsInitial (⊥_ (Arrow C)).right :=
  initialIsInitial.isInitialObj (Arrow.rightFunc : Arrow C ⥤ C)

/-- The internal map of the initial arrow is an isomorphism between initial
objects; its pushout coprojection onto the source of `Z` is also an iso. -/
private theorem initialArrow_hom_isIso :
    IsIso (⊥_ (Arrow C)).hom :=
  isIso_of_isInitial initialArrow_left_isInitial initialArrow_right_isInitial _

/-- The actual projective corner of the initial arrow is a cofibration
exactly when `Z.hom` is a cofibration. -/
private theorem initial_corner_cof_iff (Z : Arrow C) :
    cofibrations C (ProjectiveArrowFactorization.corner (initial.to Z)) ↔
      cofibrations C Z.hom := by
  letI : IsIso (⊥_ (Arrow C)).hom := initialArrow_hom_isIso
  letI : IsIso
      (pushout.inr (⊥_ (Arrow C)).hom (initial.to Z).left) := inferInstance
  have h := (cofibrations C).cancel_left_of_respectsIso
    (pushout.inr (⊥_ (Arrow C)).hom (initial.to Z).left)
    (ProjectiveArrowFactorization.corner (initial.to Z))
  simpa only [ProjectiveArrowFactorization.corner, pushout.inr_desc] using h.symm

/-- The first projective Arrow cofibration criterion for the canonical
initial map, with its literal pushout-corner definition retained. -/
theorem projective_initial_iff (Z : Arrow C) :
    ProjectiveArrowFactorization.projectiveArrowCofibrations (initial.to Z) ↔
      IsCofibrant Z.left ∧ Cofibration Z.hom := by
  have hsource : IsCofibrant Z.left ↔ Cofibration (initial.to Z).left :=
    isCofibrant_iff_of_isInitial (initial.to Z).left initialArrow_left_isInitial
  have hcorner := initial_corner_cof_iff Z
  constructor
  · intro h
    exact ⟨hsource.mpr ((cofibration_iff _).mpr h.1),
      (cofibration_iff _).mpr (hcorner.mp h.2)⟩
  · rintro ⟨hZ, hhom⟩
    exact ⟨(cofibration_iff _).mp (hsource.mp hZ),
      hcorner.mpr ((cofibration_iff _).mp hhom)⟩

omit [HasColimits C] in
/-- The same criterion in the forward direction for any chosen initial
arrow and its unique map, useful when an opposite terminal diagram supplies
an initial arrow object that is not definitionally the chosen `⊥_`. -/
theorem projective_of_isInitial (A Z : Arrow C) (hA : IsInitial A)
    (f : A ⟶ Z) (hsource : IsCofibrant Z.left) (hhom : Cofibration Z.hom) :
    ProjectiveArrowFactorization.projectiveArrowCofibrations f := by
  have hL : IsInitial A.left := hA.isInitialObj (Arrow.leftFunc : Arrow C ⥤ C)
  have hR : IsInitial A.right := hA.isInitialObj (Arrow.rightFunc : Arrow C ⥤ C)
  letI : IsIso A.hom := isIso_of_isInitial hL hR A.hom
  letI : IsIso (pushout.inr A.hom f.left) := inferInstance
  have hcorner :
      pushout.inr A.hom f.left ≫ ProjectiveArrowFactorization.corner f = Z.hom := by
    exact pushout.inr_desc _ _ _
  constructor
  · exact (cofibration_iff _).mp
      ((isCofibrant_iff_of_isInitial f.left hL).mp hsource)
  · have hcof : cofibrations C
        (pushout.inr A.hom f.left ≫ ProjectiveArrowFactorization.corner f) := by
      rw [hcorner]
      exact (cofibration_iff _).mp hhom
    exact ((cofibrations C).cancel_left_of_respectsIso
      (pushout.inr A.hom f.left) (ProjectiveArrowFactorization.corner f)).mp hcof

end

end DaggerModels.PartII.ProjectiveArrowInitial
