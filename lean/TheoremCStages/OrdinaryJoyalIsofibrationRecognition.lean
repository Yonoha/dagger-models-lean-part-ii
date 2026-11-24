import OrdinaryInnerIsoRelativeCylinder
import NativeWeakMonoRelativeWalkingHomotopy
import NativeWeakMonoQuasicategoryExtension
import NativeOriginalJoyalSmithModelData

/-!
# Recognition of the original Joyal fibrations between quasicategories

Extend a square along its actual Joyal-weak mono, connect the two images by
an exact relative walking homotopy, and lift that cylinder through the
original inner fibration. Endpoint one gives the original diagonal filler.
No candidate-fibration lifting property is assumed.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Simplicial
open DaggerActualFreeWalkingIsoIntegerObstruction
open DaggerActualFreeAntiWalkingCategoricalCylinder
open DaggerNativeWalkingHomotopySectionCorrection

universe u

namespace DaggerModels.PartII.OrdinaryJoyalIsofibrationRecognition

noncomputable section

/-- Inner-horn lifting and the actual zero-vertex lifting test recognize
the unchanged original Joyal fibration candidate between quasicategories. -/
theorem candidateFibration_of_inner_and_zero {E B : SSet.{u}}
    [E.Quasicategory] [B.Quasicategory] (p : E ⟶ B)
    (hp : DaggerNativeInnerHornFactorization.innerFibrations p)
    (hzero : HasLiftingProperty zeroInclusion.{u} p) :
    DaggerNativeJoyalFirstFactorization.candidateFibrations p := by
  intro A C i hi
  haveI : Mono i := hi.1
  constructor
  intro a b sq
  obtain ⟨g, hg⟩ :=
    DaggerNativeWeakMonoQuasicategoryExtension.weak_mono_extension i hi.2 E a
  have hsame : i ≫ (g ≫ p) = i ≫ b := by
    rw [← Category.assoc, hg]
    exact sq.w
  obtain ⟨H, h0, h1, hrel⟩ :=
    NativeWeakMonoRelativeWalkingHomotopy.exists_relative_homotopy i hi.2
      (g ≫ p) b hsame
  let cylinder : SSet.PushoutTensor i zeroInclusion.{u} :=
    Functor.PushoutObjObj.ofHasPushout _ _ _
  let left := fst C (Δ[0] : SSet.{u}) ≫ g
  let right := fst A J.{u} ≫ a
  have hw : (i ▷ (Δ[0] : SSet.{u})) ≫ left =
      (A ◁ zeroInclusion.{u}) ≫ right := by
    apply NatTrans.ext
    funext q t
    change g.app q (i.app q t.1) = a.app q t.1
    exact congrFun (NatTrans.congr_app hg q) t.1
  let top := cylinder.isPushout.desc left right hw
  have hleft : left ≫ p = (C ◁ zeroInclusion.{u}) ≫ H := by
    dsimp only [left]
    simp only [zero_whisker_endpoint, Category.assoc, h0]
  have hright : right ≫ p = (i ▷ J.{u}) ≫ H := by
    rw [hrel]
    dsimp only [right]
    rw [← Category.assoc i g p, hg]
    exact Category.assoc _ _ _
  have ht : top ≫ p = cylinder.ι ≫ H := by
    apply cylinder.isPushout.hom_ext
    · rw [← Category.assoc, IsPushout.inl_desc,
        ← Category.assoc, cylinder.inl_ι]
      exact hleft
    · rw [← Category.assoc, IsPushout.inr_desc,
        ← Category.assoc, cylinder.inr_ι]
      exact hright
  haveI : HasLiftingProperty cylinder.ι p :=
    DaggerNativeOrdinaryInnerIsoRelativeCylinder.mono_pushout_zero_lifting p hp hzero i cylinder
  let liftSquare : CommSq top cylinder.ι p H := ⟨ht⟩
  let l := intervalEndpoint C true ≫ liftSquare.lift
  refine CommSq.HasLift.mk' ⟨l, ?_, ?_⟩
  · have he : (i ▷ J.{u}) ≫ liftSquare.lift = right := by
      have hinc : cylinder.inr ≫ cylinder.ι = i ▷ J.{u} := cylinder.inr_ι
      rw [← hinc, Category.assoc, liftSquare.fac_left]
      exact cylinder.isPushout.inr_desc left right hw
    have hn : i ≫ intervalEndpoint C true =
        intervalEndpoint A true ≫ (i ▷ J.{u}) := by
      apply NatTrans.ext
      rfl
    dsimp only [l]
    rw [← Category.assoc, hn, Category.assoc, he]
    apply NatTrans.ext
    rfl
  · dsimp only [l]
    rw [Category.assoc, liftSquare.fac_right, h1]

/-- The recognized map belongs to the fibration class of the original
Smith Joyal model, rather than a newly defined lifting-only model. -/
theorem originalJoyal_fibration_of_inner_and_zero {E B : SSet.{u}}
    [E.Quasicategory] [B.Quasicategory] (p : E ⟶ B)
    (hp : DaggerNativeInnerHornFactorization.innerFibrations p)
    (hzero : HasLiftingProperty zeroInclusion.{u} p) :
    (DaggerNativeOriginalJoyalSmithModelData.modelData.model).categoryWithFibrations.fibrations p := by
  rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelFib,
    DaggerNativeFullWeakSmithGenerators.boundary_cof]
  exact candidateFibration_of_inner_and_zero p hp hzero

#print axioms candidateFibration_of_inner_and_zero
#print axioms originalJoyal_fibration_of_inner_and_zero

end
end DaggerModels.PartII.OrdinaryJoyalIsofibrationRecognition
