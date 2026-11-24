import DaggerModelsPartII.AdjunctionUnitCorners
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The unit corner at an initial source

For `L ⊣ R ⊣ S`, the composite `L ⋙ R` preserves initial objects. Its unit
component at the initial object is therefore an isomorphism. Pushing out
along `initial.to X` identifies the chosen unit corner with the literal unit
at `X` as an arrow, with identity on the target.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u v

namespace DaggerModels.PartII.AdjunctionUnitInitial

open AdjunctionUnitCorners

variable {C : Type u} {D : Type v} [Category C] [Category D]
  {L : C ⥤ D} {R : D ⥤ C} {S : C ⥤ D}
  (adjLR : L ⊣ R) (adjRS : R ⊣ S)

include adjRS

noncomputable section

/-- The left-adjoint endofunctor preserves the initial object. -/
private def composite_initial [HasInitial C] :
    IsInitial ((L ⋙ R).obj (⊥_ C)) := by
  letI : (L ⋙ R).IsLeftAdjoint :=
    ⟨S ⋙ R, ⟨adjLR.comp adjRS⟩⟩
  exact (initialIsInitial : IsInitial (⊥_ C)).isInitialObj (L ⋙ R)

/-- The unit component at an initial object is an isomorphism because both
its source and target are initial. -/
theorem unit_initial_isIso [HasInitial C] :
    IsIso (adjLR.unit.app (⊥_ C)) := by
  let e := (initialIsInitial : IsInitial (⊥_ C)).uniqueUpToIso
    (composite_initial adjLR adjRS)
  have h : adjLR.unit.app (⊥_ C) = e.hom :=
    (initialIsInitial : IsInitial (⊥_ C)).hom_ext _ _
  rw [h]
  infer_instance

/-- The chosen corner's map from `X` is an isomorphism when the source map
starts at the initial object. -/
theorem unitPushoutCorner_initial_inr_isIso
    [HasInitial C] [HasPushouts C] (X : C) :
    IsIso (unitPushoutCorner adjLR (initial.to X)).inr := by
  letI : IsIso (adjLR.unit.app (⊥_ C)) :=
    unit_initial_isIso adjLR adjRS
  exact (unitPushoutCorner_isPushout adjLR (initial.to X)).isIso_inr_of_isIso

/-- The literal unit arrow is isomorphic to the actual corner at
`initial.to X`, using the corner's `inr` on sources and identity on targets. -/
def unitPushoutCorner_initial_arrowIso
    [HasInitial C] [HasPushouts C] (X : C) :
    Arrow.mk (adjLR.unit.app X) ≅
      Arrow.mk (unitPushoutCorner adjLR (initial.to X)).ι := by
  letI : IsIso (unitPushoutCorner adjLR (initial.to X)).inr :=
    unitPushoutCorner_initial_inr_isIso adjLR adjRS X
  refine Arrow.isoMk
    (asIso (unitPushoutCorner adjLR (initial.to X)).inr)
    (Iso.refl ((L ⋙ R).obj X)) ?_
  change (unitPushoutCorner adjLR (initial.to X)).inr ≫
    (unitPushoutCorner adjLR (initial.to X)).ι =
      adjLR.unit.app X ≫ 𝟙 ((L ⋙ R).obj X)
  simpa only [Category.comp_id] using
    (unitPushoutCorner_inr_ι adjLR (initial.to X))

end

end DaggerModels.PartII.AdjunctionUnitInitial
