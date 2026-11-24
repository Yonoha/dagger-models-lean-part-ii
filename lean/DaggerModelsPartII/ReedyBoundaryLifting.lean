import DaggerModelsPartII.ReedyBoundaryTensor
import DaggerModelsPartII.ExternalTensorPresentability
import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction

/-! The outer boundary pushout-product tests the relative matching map. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerModels.PartII

noncomputable section

local instance boundaryLiftingCoefficientLimits : HasLimits DaggerSSet.{u} := daggerSSetHasLimits
local instance boundaryLiftingCoefficientColimits : HasColimits DaggerSSet.{u} := daggerSSetHasColimits

/-- The boundary tensor is left adjoint to the matching-object functor. -/
def boundaryTensorAdjunction (n : ℕ) :
    externalTensorWith (SSet.boundary.{u} n).toSSet ⊣ matchingFunctor n :=
  Adjunction.mkOfHomEquiv
    { homEquiv := boundaryTensorHomEquiv n
      homEquiv_naturality_left_symm := by
        intro A B W i q
        apply (boundaryTensorHomEquiv n A W).injective
        rw [Equiv.apply_symm_apply, boundaryTensorHomEquiv_natural_left, Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun f g ↦ boundaryTensorHomEquiv_natural_right n f g }

/-- The outer boundary inclusion, natural in the coefficient object. -/
def boundaryTensorInclusion (n : ℕ) :
    externalTensorWith (SSet.boundary.{u} n).toSSet ⟶ externalTensorWith Δ[n] :=
  Functor.whiskerLeft _ ((Functor.whiskeringLeft _ _ _).map (SSet.boundary n).ι)

-- The two nonidentity arrows of the parameter category both encode the same inclusion.
private def boundaryParameterLeft (n : ℕ) : WalkingParallelPair ⥤
    DaggerSSet.{u} ⥤ ResolutionDiagram.{u} :=
  parallelPair (boundaryTensorInclusion n) (boundaryTensorInclusion n)

private def boundaryParameterRight (n : ℕ) : WalkingParallelPairᵒᵖ ⥤
    ResolutionDiagram.{u} ⥤ DaggerSSet.{u} :=
  walkingParallelPairOpEquiv.inverse ⋙ parallelPair (matchingComparison n) (matchingComparison n)

private def boundaryParameterAdjunctionAt (n : ℕ) (s : WalkingParallelPair) :
    (boundaryParameterLeft.{u} n).obj s ⊣ (boundaryParameterRight n).obj (op s) :=
  match s with
  | .zero => boundaryTensorAdjunction n
  | .one => evaluationAdjunction n

private def boundaryParameterAdjunction (n : ℕ) :
    boundaryParameterLeft.{u} n ⊣₂ boundaryParameterRight n :=
  ParametrizedAdjunction.mk' (boundaryParameterAdjunctionAt n) (by
    intro s t g A W q
    cases g with
    | left =>
      simpa only [boundaryParameterAdjunctionAt, boundaryTensorAdjunction, evaluationAdjunction,
        Adjunction.mkOfHomEquiv_homEquiv] using boundaryTensorHomEquiv_restrict n q
    | right =>
      simpa only [boundaryParameterAdjunctionAt, boundaryTensorAdjunction, evaluationAdjunction,
        Adjunction.mkOfHomEquiv_homEquiv] using boundaryTensorHomEquiv_restrict n q
    | id s =>
      cases s <;>
        change _ = _ ≫ 𝟙 _ <;>
        simp [boundaryParameterLeft, boundaryParameterRight, Category.id_comp])

private def boundaryBoxPushout (n : ℕ) {A B : DaggerSSet.{u}} (i : A ⟶ B) :
    (boundaryParameterLeft n).PushoutObjObj WalkingParallelPairHom.left i :=
  Functor.PushoutObjObj.ofHasPushout _ _ _

/-- The pushout-product of the outer boundary inclusion with a coefficient map. -/
def reedyBoundaryBox (n : ℕ) {A B : DaggerSSet.{u}} (i : A ⟶ B) :=
  (boundaryBoxPushout n i).ι

/-- Both objects of the boundary pushout-product are finitely presentable when
the coefficient map has finitely presentable endpoints. -/
theorem reedyBoundaryBox_finitelyPresentable (n : ℕ) {A B : DaggerSSet.{u}} (i : A ⟶ B)
    [IsFinitelyPresentable.{u} A] [IsFinitelyPresentable.{u} B] :
    IsFinitelyPresentable.{u} (Arrow.mk (reedyBoundaryBox n i)).left ∧
      IsFinitelyPresentable.{u} (Arrow.mk (reedyBoundaryBox n i)).right := by
  let sq := boundaryBoxPushout n i
  letI := Cardinal.fact_isRegular_aleph0.{u}
  refine ⟨?_, externalTensor_obj_isFinitelyPresentable B Δ[n]⟩
  change IsFinitelyPresentable.{u} sq.pt
  apply (config := { allowSynthFailures := true })
    isCardinalPresentable_of_isColimit' _ sq.isPushout.isColimit Cardinal.aleph0.{u}
  · exact hasCardinalLT_of_finite (Arrow WalkingSpan) _ le_rfl
  · rintro (_ | _ | _)
    · exact externalTensor_obj_isFinitelyPresentable A (SSet.boundary n).toSSet
    · exact externalTensor_obj_isFinitelyPresentable A Δ[n]
    · exact externalTensor_obj_isFinitelyPresentable B (SSet.boundary n).toSSet

private def boundaryMatchingPullback (n : ℕ) {X Y : ResolutionDiagram.{u}} (f : X ⟶ Y) :
    (boundaryParameterRight n).PullbackObjObj WalkingParallelPairHom.left f :=
  Functor.PullbackObjObj.ofHasPullback _ _ _

private theorem boundaryMatchingPullback_π (n : ℕ) {X Y : ResolutionDiagram.{u}} (f : X ⟶ Y) :
    (boundaryMatchingPullback n f).π = relativeMatchingMap n f := by
  apply pullback.hom_ext
  · exact ((boundaryMatchingPullback n f).π_fst).trans (pullback.lift_fst _ _ _).symm
  · exact ((boundaryMatchingPullback n f).π_snd).trans (pullback.lift_snd _ _ _).symm

/-- A boundary pushout-product has exactly the lifting test given by relative matching. -/
theorem reedyBoundaryBox_hasLiftingProperty_iff (n : ℕ)
    {A B : DaggerSSet.{u}} (i : A ⟶ B) {X Y : ResolutionDiagram.{u}} (f : X ⟶ Y) :
    HasLiftingProperty (reedyBoundaryBox n i) f ↔
      HasLiftingProperty i (relativeMatchingMap n f) := by
  rw [← boundaryMatchingPullback_π]
  exact (boundaryParameterAdjunction n).hasLiftingProperty_iff
    (boundaryBoxPushout n i) (boundaryMatchingPullback n f)

end

end DaggerModels.PartII
