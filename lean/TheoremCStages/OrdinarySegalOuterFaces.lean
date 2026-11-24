import OrdinarySpineModelOuterFaces
import OrdinarySegalLocalization
import OrdinarySegalSpineTwoPullback

/-!
# Outer-face inclusions in the ordinary Segal model

Apply the spine-only outer-face theorem to the checked Segal localization.
The argument uses no walking-isomorphism completeness localizer.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Simplicial
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalOuterFaces

open OrdinaryCSSLocalization (Space discrete spineMap)
open OrdinarySegalLocalization (model)

noncomputable section

private local instance : ModelCategory Space := model

/-- Cofibrations in the ordinary Segal model are exactly monomorphisms. -/
theorem cofibrations_eq_monomorphisms :
    model.categoryWithCofibrations.cofibrations = monomorphisms Space :=
  OrdinarySegalLocalization.exactClasses.1.trans
    (InjectiveKanDiagram.model_cofibrations SimplexCategoryᵒᵖ)

/-- Every dimension of the literal spine inclusion is Segal weak. -/
theorem spine_weak (n : ℕ) :
    model.categoryWithWeakEquivalences.weakEquivalences
      (discrete.map (DaggerNativeStandardSpineInner.spine n).ι) := by
  by_cases hn : 2 ≤ n
  · exact OrdinarySegalLocalization.spineMap_weak n hn
  · have hsmall : n ≤ 1 := by omega
    have : IsIso (DaggerNativeStandardSpineInner.spine.{0} n).ι := by
      rw [← OrdinarySegalSpineTwoPullback.smallSpineIso_hom n hsmall]
      infer_instance
    have : IsIso (discrete.map (DaggerNativeStandardSpineInner.spine n).ι) :=
      Functor.map_isIso _ _
    exact (weakEquivalences Space).of_isIso _

private theorem leftProper : OrdinarySpineModelOuterFaces.LeftProper model := by
  intro A B D P i k l r sq hi hw
  exact InjectiveKanDiagram.localized_leftProper SimplexCategoryᵒᵖ
    OrdinarySegalLocalization.LocalizerIndex OrdinarySegalLocalization.localizerArrow
    OrdinarySegalLocalization.localizerArrow_mono sq hi hw

/-- The original union of the two outer faces is weak before imposing completeness. -/
theorem outerFace_weak (t : ℕ) :
    model.categoryWithWeakEquivalences.weakEquivalences
      (discrete.map (ReversalOuterFaceLocality.ordinaryOuterFaces t).ι) :=
  OrdinarySpineModelOuterFaces.outerFace_weak model
    cofibrations_eq_monomorphisms spine_weak leftProper t

/-- The same literal outer-face map is a Segal trivial cofibration. -/
theorem outerFace_trivialCofibration (t : ℕ) :
    @trivialCofibrations Space _ model.categoryWithCofibrations
      model.categoryWithWeakEquivalences _ _
      (discrete.map (ReversalOuterFaceLocality.ordinaryOuterFaces t).ι) := by
  refine ⟨?_, outerFace_weak t⟩
  change model.categoryWithCofibrations.cofibrations
    (discrete.map (ReversalOuterFaceLocality.ordinaryOuterFaces t).ι)
  rw [cofibrations_eq_monomorphisms]
  exact OrdinaryCSSLocalization.discrete_map_mono _

#print axioms spine_weak
#print axioms outerFace_weak
#print axioms outerFace_trivialCofibration

end

end DaggerModels.PartII.OrdinarySegalOuterFaces
