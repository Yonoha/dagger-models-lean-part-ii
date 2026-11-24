import SSetSM7
import NativeKanTrivialCofibrationRestriction

/-!
# Simultaneous relative lifting in two simplicial parameters
-/

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.JTParametricRelativeExtension

variable {A B L K X Y : SSet.{u}}

/-- The full pushout product lifts against a Kan fibration if either inclusion
is a Kan weak equivalence, or if the fibration is a weak equivalence. -/
theorem pushoutTensor_lifts (i : A ⟶ B) [Mono i] (j : L ⟶ K) [Mono j]
    (p : X ⟶ Y) [Fibration p]
    (h : WeakEquivalence i ∨ WeakEquivalence j ∨ WeakEquivalence p) :
    HasLiftingProperty (DaggerSSetSM7.pushoutTensor i j).ι p := by
  rcases h with hi | hj | hp
  · letI := hi
    letI : Cofibration i := SSet.modelCategoryQuillen.cofibration_of_mono i
    exact (SSet.anodyneExtensions.pushoutTensorι₁ _
      (DaggerNativeKanTrivialCofibrationRestriction.trivial_anodyne i)).hasLeftLiftingProperty p
  · letI := hj
    letI : Cofibration j := SSet.modelCategoryQuillen.cofibration_of_mono j
    exact (SSet.anodyneExtensions.pushoutTensorι₂ _
      (DaggerNativeKanTrivialCofibrationRestriction.trivial_anodyne j)).hasLeftLiftingProperty p
  · letI := hp
    rw [DaggerSSetSM7.pushoutTensor_ι]
    letI := DaggerSSetSM7.pushoutProduct_mono i j
    infer_instance

/-- Extend both prescribed subcomplexes with their exact restrictions and
the prescribed map to the base. The input maps agree on the entire product
of the two subcomplexes. -/
theorem exists_extension (i : A ⟶ B) [Mono i] (j : L ⟶ K) [Mono j]
    (p : X ⟶ Y) [Fibration p]
    (h : WeakEquivalence i ∨ WeakEquivalence j ∨ WeakEquivalence p)
    (bottom : B ⊗ K ⟶ Y) (gB : B ⊗ L ⟶ X) (gA : A ⊗ K ⟶ X)
    (hcompat : (i ▷ L) ≫ gB = (A ◁ j) ≫ gA)
    (hB : gB ≫ p = (B ◁ j) ≫ bottom)
    (hA : gA ≫ p = (i ▷ K) ≫ bottom) :
    ∃ F : B ⊗ K ⟶ X, (B ◁ j) ≫ F = gB ∧ (i ▷ K) ≫ F = gA ∧ F ≫ p = bottom := by
  let sq := DaggerSSetSM7.pushoutTensor i j
  let top : sq.pt ⟶ X := sq.isPushout.desc gB gA hcompat
  have htop : top ≫ p = sq.ι ≫ bottom := by
    apply sq.isPushout.hom_ext
    · rw [← Category.assoc, IsPushout.inl_desc, ← Category.assoc, sq.inl_ι]
      exact hB
    · rw [← Category.assoc, IsPushout.inr_desc, ← Category.assoc, sq.inr_ι]
      exact hA
  letI : HasLiftingProperty sq.ι p := pushoutTensor_lifts i j p h
  let c : CommSq top sq.ι p bottom := ⟨htop⟩
  refine ⟨c.lift, ?_, ?_, c.fac_right⟩
  · have hleg : sq.inl ≫ sq.ι = (B ◁ j) := sq.inl_ι
    rw [← hleg, Category.assoc, c.fac_left]
    exact sq.isPushout.inl_desc gB gA hcompat
  · have hleg : sq.inr ≫ sq.ι = (i ▷ K) := sq.inr_ι
    rw [← hleg, Category.assoc, c.fac_left]
    exact sq.isPushout.inr_desc gB gA hcompat

end DaggerModels.PartII.JTParametricRelativeExtension
