import OriginalRLPAccessibilityRecovered
import OriginalAccessibleInverseImageRecovered
import OriginalAccessibleSolutionsRecovered
import OriginalSOAFactorizationRecovered
import OriginalSmithCardinalRecovered
import Mathlib.AlgebraicTopology.ModelCategory.Basic
import Mathlib.CategoryTheory.Limits.Comma

/-! Accessibility of weak equivalences from accessible small-object factorization. -/

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

universe w v u

namespace DaggerModels.PartII.ModelWeakAccessibility

noncomputable section

variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]
  [LocallySmall.{w} C] [HasColimitsOfSize.{w, w} C]
  (I J : MorphismProperty C) [IsSmall.{w} I] [IsSmall.{w} J]

private structure Rank where
  κ : Cardinal.{w}
  regular : κ.IsRegular
  left : ∀ r : J.toSet, @IsCardinalPresentable _ _ r.1.left κ ⟨regular⟩
  right : ∀ r : J.toSet, @IsCardinalPresentable _ _ r.1.right κ ⟨regular⟩

private def rank : Rank J := by
  let A : J.toSet ⊕ J.toSet → C := Sum.elim (fun r ↦ r.1.left) (fun r ↦ r.1.right)
  let h := DaggerSmithSolutionSet.uniformPresentability A
  exact ⟨h.choose, h.choose_spec.choose, fun r ↦ h.choose_spec.choose_spec (.inl r),
    fun r ↦ h.choose_spec.choose_spec (.inr r)⟩

local instance rankRegular : Fact (rank J).κ.IsRegular := ⟨(rank J).regular⟩
local instance rankOrderBot : OrderBot (rank J).κ.ord.ToType :=
  Cardinal.toTypeOrderBot (rank J).regular.ne_zero

local instance coproducts : HasCoproducts.{w} C := by
  intro K
  exact (inferInstance : HasColimitsOfSize.{w, w} C).has_colimits_of_shape (Discrete K)

local instance rankSuitable : J.IsCardinalForSmallObjectArgument (rank J).κ where
  preservesColimit := by
    intro A B X Y i hi f hf
    let r : J.toSet := ⟨Arrow.mk i, hi⟩
    letI : IsCardinalPresentable A (rank J).κ := (rank J).left r
    have := preservesColimitsOfShape_of_isCardinalPresentable A (rank J).κ (rank J).κ.ord.ToType
    infer_instance

private def factorization : FunctorialFactorizationData J.rlp.llp J.rlp :=
  SmallObject.functorialFactorizationData J (rank J).κ

/-- The accessible right-factor functor of the small object factorization at `J`. -/
def rightFactor : Arrow C ⥤ Arrow C :=
  DaggerSOAAccessible.rightFactor (factorization J)

theorem rightFactor_accessible : Functor.IsAccessible.{w} (rightFactor J) := by
  let κ := (rank J).κ
  letI : ∀ r : J.toSet, IsCardinalPresentable r.1.left κ := (rank J).left
  letI : ∀ r : J.toSet, IsCardinalPresentable r.1.right κ := (rank J).right
  letI : (rightFactor J).IsCardinalAccessible κ :=
    DaggerSOAStepAccessible.property_rightFactor_accessible J κ
  exact Functor.isAccessible_of_isCardinalAccessible _ κ

/-- The same accessible small-object factorization, including its natural left map. -/
def accessibleFactorization : FunctorialFactorizationData J.rlp.llp J.rlp :=
  factorization J

/-- The middle-object functor of this particular factorization is accessible. -/
theorem accessibleFactorization_Z_accessible :
    Functor.IsAccessible.{w} (accessibleFactorization J).Z := by
  letI := rightFactor_accessible J
  obtain ⟨κ, hκ, hR⟩ := (rightFactor_accessible J).exists_cardinal
  letI := hκ
  letI := hR
  letI : (Arrow.leftFunc : Arrow C ⥤ C).IsCardinalAccessible κ := by
    constructor
    intro T _ _
    letI : HasColimitsOfShape T C :=
      (inferInstance : HasColimitsOfSize.{w, w} C).has_colimits_of_shape T
    exact Arrow.preservesColimitsOfShape_leftFunc
  change Functor.IsAccessible.{w} (rightFactor J ⋙ Arrow.leftFunc)
  exact Functor.isAccessible_of_isCardinalAccessible _ κ

omit [IsSmall.{w} I] in
/-- A map is weak precisely when the right factor belongs to the right orthogonal
of the generating cofibrations. -/
theorem weakArrow_eq_inverseImage
    (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C) :
    DaggerAccessibleSolutions.arrowProperty (weakEquivalences C) =
      (DaggerRLPAccessibility.rightOrthogonal I).inverseImage (rightFactor J) := by
  have hleft : J.rlp.llp = trivialCofibrations C := by
    rw [hJ]
    exact llp_eq_of_wfs (trivialCofibrations C) (fibrations C)
  funext f
  apply propext
  change weakEquivalences C f.hom ↔ I.rlp ((factorization J).p.app f)
  rw [hI]
  have hi : trivialCofibrations C ((factorization J).i.app f) :=
    hleft ▸ (factorization J).hi f
  have hp : fibrations C ((factorization J).p.app f) := hJ ▸ (factorization J).hp f
  change weakEquivalences C f.hom ↔
    fibrations C ((factorization J).p.app f) ∧ weakEquivalences C ((factorization J).p.app f)
  constructor
  · intro hf
    refine ⟨hp, (weakEquivalences C).of_precomp _ _ hi.2 ?_⟩
    simpa using hf
  · rintro ⟨_, hf⟩
    have h := (weakEquivalences C).comp_mem _ _ hi.2 hf
    simpa using h

/-- The weak-equivalence arrow category and its inclusion are accessible. -/
theorem weakArrow_accessibility
    (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C) :
    ∃ τ : Cardinal.{w}, ∃ _ : Fact τ.IsRegular,
      ∃ R : ObjectProperty (DaggerAccessibleSolutions.arrowProperty
          (weakEquivalences C)).FullSubcategory,
        ObjectProperty.Small.{w} R ∧ R.IsCardinalFilteredGenerator τ ∧
          IsCardinalAccessibleCategory (DaggerAccessibleSolutions.arrowProperty
            (weakEquivalences C)).FullSubcategory τ ∧
          (DaggerAccessibleSolutions.arrowProperty
            (weakEquivalences C)).ι.IsCardinalAccessible τ := by
  letI := DaggerRLPAccessibility.arrowLocallyPresentable C
  let P := DaggerRLPAccessibility.rightOrthogonal I
  let E := DaggerRLPAccessibility.property_accessibility I
  let τ := E.choose
  letI : Fact τ.IsRegular := E.choose_spec.choose
  have hdata := E.choose_spec.choose_spec.choose_spec
  letI : IsCardinalAccessibleCategory P.FullSubcategory τ := hdata.2.2.1
  letI : P.ι.IsCardinalAccessible τ := hdata.2.2.2
  letI : IsAccessibleCategory.{w} P.FullSubcategory :=
    ⟨⟨τ, inferInstance, inferInstance⟩⟩
  letI : Functor.IsAccessible.{w} P.ι := Functor.isAccessible_of_isCardinalAccessible _ τ
  letI : P.IsClosedUnderIsomorphisms := by
    constructor
    intro A B e h
    exact (I.rlp.arrow_iso_iff e).mp h
  letI : Functor.IsAccessible.{w} (rightFactor J) := rightFactor_accessible J
  rw [weakArrow_eq_inverseImage I J hI hJ]
  exact DaggerAccessibleInverseImage.accessible_inverseImage (rightFactor J) P

/-- Accessibility of the full subcategory of weak-equivalence arrows. -/
theorem weakArrow_isAccessible
    (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C) :
    IsAccessibleCategory.{w}
      (DaggerAccessibleSolutions.arrowProperty (weakEquivalences C)).FullSubcategory := by
  obtain ⟨κ, hκ, R, hsmall, hgen, hcat, hincl⟩ := weakArrow_accessibility I J hI hJ
  exact ⟨⟨κ, hκ, hcat⟩⟩

/-- Accessibility of the inclusion of weak-equivalence arrows into all arrows. -/
theorem weakArrow_inclusion_isAccessible
    (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C) :
    Functor.IsAccessible.{w}
      (DaggerAccessibleSolutions.arrowProperty (weakEquivalences C)).ι := by
  obtain ⟨κ, hκ, R, hsmall, hgen, hcat, hincl⟩ := weakArrow_accessibility I J hI hJ
  letI := hκ
  letI := hincl
  exact Functor.isAccessible_of_isCardinalAccessible _ κ

end

end DaggerModels.PartII.ModelWeakAccessibility
