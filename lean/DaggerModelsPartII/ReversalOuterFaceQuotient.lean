import DaggerModelsPartII.OuterFaceLocalEquivalence
import DaggerModelsPartII.OuterFaceYonedaComparison
import DaggerModelsPartII.ReversalOuterFaceAction
import DaggerModelsPartII.DiscreteBorelTheorem

/-!
# Local trivial cofibrations on outer faces and their reversal quotients

The literal Yoneda outer-face union is identified with the discrete free
dagger outer-face inclusion. The Borel comparison then applies to its actual
representable reversal action, with no extra local-equivalence hypothesis.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra MorphismProperty

namespace DaggerModels.PartII.ReversalOuterFaceQuotient

open SegalLocalizers ReversalOuterFaceSubobject ReversalOuterFaceAction
open OuterFaceYonedaComparison C2InvolutionActions DiscreteBorelDiagram

noncomputable section

/-- The literal Yoneda outer-face inclusion is a local trivial cofibration. -/
theorem discreteOuterFaceInclusion_localTrivial (t : ℕ) :
    injectiveSegalModel.categoryWithCofibrations.cofibrations
        (discreteDiagram.map (outerFaceSubpresheafAt (t + 2) (by omega)).ι) ∧
      injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
        (discreteDiagram.map (outerFaceSubpresheafAt (t + 2) (by omega)).ι) := by
  letI : ModelCategory ReverseDaggerSpace.{0} := injectiveSegalModel
  have h := OuterFaceLocalEquivalence.daggerOuterFaceMap_trivialCofibration t
  let e : Arrow.mk (ReversalOuterFaceLocality.daggerOuterFaceMap.{0} t) ≅
      Arrow.mk (discreteDiagram.map
        (outerFaceSubpresheafAt (t + 2) (by omega)).ι) :=
    Arrow.isoMk (daggerOuterFacesYonedaIso t) (daggerSimplexYonedaIso (t + 2))
      (daggerOuterFacesYonedaIso_natural t).symm
  exact ⟨((cofibrations ReverseDaggerSpace.{0}).arrow_mk_iso_iff e).mp h.1,
    ((weakEquivalences ReverseDaggerSpace.{0}).arrow_mk_iso_iff e).mp h.2⟩

/-- Taking strict reversal orbits of the outer-face union remains a local
trivial cofibration, as required for the palindromic cells. -/
theorem outerFaceStrictOrbitInclusion_localTrivial (t : ℕ) :
    injectiveSegalModel.categoryWithCofibrations.cofibrations
        (subsetStrictOrbitInclusion (yoneda.obj (⟨t + 2⟩ : ReverseSimplex))
          (representableReversalIso (t + 2)) (representableReversal_involutive (t + 2))
          (outerFaceSubpresheafAt (t + 2) (by omega))
          (outerFace_invariant (t + 2) (by omega))) ∧
      injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
        (subsetStrictOrbitInclusion (yoneda.obj (⟨t + 2⟩ : ReverseSimplex))
          (representableReversalIso (t + 2)) (representableReversal_involutive (t + 2))
          (outerFaceSubpresheafAt (t + 2) (by omega))
          (outerFace_invariant (t + 2) (by omega))) :=
  DiscreteBorelTheorem.reversal_strictOrbitInclusion_localTrivial
    (yoneda.obj (⟨t + 2⟩ : ReverseSimplex))
    (representableReversalIso (t + 2)) (representableReversal_involutive (t + 2))
    (outerFaceSubpresheafAt (t + 2) (by omega))
    (outerFace_invariant (t + 2) (by omega)) (outerFace_fixed (t + 2) (by omega))
    (discreteOuterFaceInclusion_localTrivial t).2

/-- The same outer-face quotient inclusion expressed using the native
categorical strict-orbit functor. -/
theorem outerFaceNativeStrictOrbitInclusion_localTrivial (t : ℕ) :
    injectiveSegalModel.categoryWithCofibrations.cofibrations
        ((ActionStrictOrbits.orbit ReverseDaggerSpace.{0}
          DaggerOriginalDaggerRealizationC2Action.C2.{0}).map
          (discreteSubsetInclusion (yoneda.obj (⟨t + 2⟩ : ReverseSimplex))
            (representableReversalIso (t + 2)) (representableReversal_involutive (t + 2))
            (outerFaceSubpresheafAt (t + 2) (by omega))
            (outerFace_invariant (t + 2) (by omega)))) ∧
      injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
        ((ActionStrictOrbits.orbit ReverseDaggerSpace.{0}
          DaggerOriginalDaggerRealizationC2Action.C2.{0}).map
          (discreteSubsetInclusion (yoneda.obj (⟨t + 2⟩ : ReverseSimplex))
            (representableReversalIso (t + 2)) (representableReversal_involutive (t + 2))
            (outerFaceSubpresheafAt (t + 2) (by omega))
            (outerFace_invariant (t + 2) (by omega)))) :=
  DiscreteBorelTheorem.nativeStrictOrbitInclusion_localTrivial ReverseSimplexᵒᵖ
    LocalizerIndex localizerArrow localizerArrow_mono
    (yoneda.obj (⟨t + 2⟩ : ReverseSimplex))
    (representableReversalIso (t + 2)) (representableReversal_involutive (t + 2))
    (outerFaceSubpresheafAt (t + 2) (by omega))
    (outerFace_invariant (t + 2) (by omega)) (outerFace_fixed (t + 2) (by omega))
    (discreteOuterFaceInclusion_localTrivial t).2

end

end DaggerModels.PartII.ReversalOuterFaceQuotient
