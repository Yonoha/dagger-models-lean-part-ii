import DaggerModelsPartII.LocalEquivalenceClasses
import DaggerModelsPartII.ArrowAccessibility
import OriginalAccessibleInverseImageRecovered
import OriginalAccessibleSolutionsRecovered
import OriginalRLPAccessibilityRecovered

/-!
# Solution sets from accessible local replacement

An accessible functorial local replacement detects exactly the local weak
equivalences by the original weak-equivalence class. Accessibility of the
original weak-arrow category therefore supplies a small Smith solution set
for the literal local-equivalence class.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

universe w v u

namespace DaggerModels.PartII.Localization

noncomputable section

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [IsLocallyPresentable.{w} C] [LocallySmall.{w} C]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]
  [HasColimitsOfSize.{w, w} C]

/-- Accessible local replacement and accessible original weak arrows yield a
small solution set for the exact local weak-equivalence class. -/
def localReplacementSolutionSet
    (S I : MorphismProperty C) [IsSmall.{w} I]
    (R : C ⥤ C) (η : 𝟭 C ⟶ R)
    (hR : ∀ X, localObject S (R.obj X))
    (hη : ∀ X, localEquivalences S (η.app X))
    (hRAccessible : Functor.IsAccessible.{w} R)
    (hWeakAccessible : IsAccessibleCategory.{w}
      (DaggerAccessibleSolutions.arrowProperty (weakEquivalences C)).FullSubcategory)
    (hWeakInclusionAccessible : Functor.IsAccessible.{w}
      (DaggerAccessibleSolutions.arrowProperty (weakEquivalences C)).ι) :
    DaggerSmithSolutionSet.SolutionData.{w} I (localEquivalences S) := by
  letI := DaggerRLPAccessibility.arrowLocallyPresentable C
  let W := DaggerAccessibleSolutions.arrowProperty (weakEquivalences C)
  let F := R.mapArrow
  letI : W.IsClosedUnderIsomorphisms := by
    constructor
    intro A B e h
    exact ((weakEquivalences C).arrow_iso_iff e).mp h
  let E := hRAccessible.exists_cardinal
  let κ := E.choose
  let hκ := E.choose_spec.choose
  let hRc := E.choose_spec.choose_spec
  letI := hκ
  letI := hRc
  letI : F.IsCardinalAccessible κ := mapArrow_isCardinalAccessible R κ
  letI : Functor.IsAccessible.{w} F :=
    Functor.isAccessible_of_isCardinalAccessible F κ
  letI : IsAccessibleCategory.{w} W.FullSubcategory := hWeakAccessible
  letI : Functor.IsAccessible.{w} W.ι := hWeakInclusionAccessible
  have he : DaggerAccessibleSolutions.arrowProperty (localEquivalences S) =
      W.inverseImage F := by
    rw [localEquivalences_eq_inverseImage S R η hR hη]
    rfl
  letI : IsAccessibleCategory.{w}
      (DaggerAccessibleSolutions.arrowProperty (localEquivalences S)).FullSubcategory :=
    he.symm ▸ DaggerAccessibleInverseImage.inverseImage_isAccessible F W
  letI : Functor.IsAccessible.{w}
      (DaggerAccessibleSolutions.arrowProperty (localEquivalences S)).ι :=
    he.symm ▸ DaggerAccessibleInverseImage.inverseImage_inclusion_isAccessible F W
  exact DaggerAccessibleSolutions.ofAccessible I (localEquivalences S)

end

end DaggerModels.PartII.Localization
