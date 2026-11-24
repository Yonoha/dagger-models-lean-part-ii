import OrdinaryCSSLocalization
import DaggerModelsPartII.OuterFaceSpineGeometry
import DaggerModelsPartII.LeftProperPushoutComparison

/-!
# Outer-face locality from the literal spine maps

The standard outer-face pushout proof is parameterized by its actual inputs:
a model on ordinary simplicial spaces with monomorphism cofibrations, weak
spine inclusions, and left properness. This reuses the existing spine-part
geometry and the checked pushout-comparison theorem. Completeness is absent
from the hypotheses, allowing application to the ordinary Segal model.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty

namespace DaggerModels.PartII.OrdinarySpineModelOuterFaces

open OrdinaryCSSLocalization (Space discrete)
open SpineOuterFacePushout OuterFaceSpineGeometry ReversalOuterFaceLocality

noncomputable section

private instance : PreservesColimitsOfShape WalkingSpan discrete := by
  letI : PreservesColimitsOfShape WalkingSpan (SimplicialObject.const (Type 0)) :=
    (CategoryTheory.Limits.preservesColimits_const
      (D := SimplexCategoryᵒᵖ)).preservesColimitsOfShape
  change PreservesColimitsOfShape WalkingSpan
    ((Functor.whiskeringRight SimplexCategoryᵒᵖ (Type 0) SSet.{0}).obj
      (SimplicialObject.const (Type 0)))
  infer_instance

variable (N : ModelCategory Space)

private local instance : ModelCategory Space := N

/-- The actual left properness input, with the chosen model kept explicit. -/
def LeftProper : Prop :=
  ∀ {A B D P : Space} {i : A ⟶ B} {k : A ⟶ D} {l : B ⟶ P} {r : D ⟶ P},
    IsPushout i k l r → N.categoryWithCofibrations.cofibrations i →
      N.categoryWithWeakEquivalences.weakEquivalences k →
        N.categoryWithWeakEquivalences.weakEquivalences l

/-- Weak spine maps and their literal pushout presentation imply outer-face locality. -/
theorem outerFace_weak
    (hcof : N.categoryWithCofibrations.cofibrations = monomorphisms Space)
    (hspine : ∀ n : ℕ, N.categoryWithWeakEquivalences.weakEquivalences
      (discrete.map (DaggerNativeStandardSpineInner.spine n).ι))
    (hproper : LeftProper N) (t : ℕ) :
    N.categoryWithWeakEquivalences.weakEquivalences
      (discrete.map (ordinaryOuterFaces t).ι) := by
  have hc {A B : SSet.{0}} (i : A ⟶ B) [Mono i] :
      cofibrations Space (discrete.map i) := by
    change N.categoryWithCofibrations.cofibrations (discrete.map i)
    rw [hcof]
    exact OrdinaryCSSLocalization.discrete_map_mono i
  have hm : weakEquivalences Space (discrete.map (middleVertical t)) :=
    ((weakEquivalences Space).arrow_mk_iso_iff
      (discrete.mapArrow.mapIso (middleVerticalArrowIso t))).mp (hspine t)
  have hf : weakEquivalences Space (discrete.map (firstVertical t)) :=
    ((weakEquivalences Space).arrow_mk_iso_iff
      (discrete.mapArrow.mapIso (firstVerticalArrowIso t))).mp (hspine (t + 1))
  have hl : weakEquivalences Space (discrete.map (lastVertical t)) :=
    ((weakEquivalences Space).arrow_mk_iso_iff
      (discrete.mapArrow.mapIso (lastVerticalArrowIso t))).mp (hspine (t + 1))
  have hfactor : weakEquivalences Space (discrete.map (spineToOuterFaces t)) := by
    apply weak_of_pushoutComparison hproper
      ((spinePartsPushout.{0} t).map discrete)
      ((outerFacePushout.{0} t).map discrete)
      (hc (SSet.Subcomplex.homOfLE
        (inf_le_left : middleSpinePart.{0} t ≤ firstSpinePart t)))
      (hc (SSet.Subcomplex.homOfLE
        (inf_le_left : middleFace.{0} t ≤ firstOuterFace t)))
      (discrete.map (middleVertical t)) (discrete.map (firstVertical t))
      (discrete.map (lastVertical t)) (discrete.map (spineToOuterFaces t))
    · simp only [← discrete.map_comp]
      rfl
    · simp only [← discrete.map_comp]
      rfl
    · simp only [← discrete.map_comp]
      rfl
    · simp only [← discrete.map_comp]
      rfl
    · exact hm
    · exact hf
    · exact hl
  apply (weakEquivalences Space).of_precomp
    (discrete.map (spineToOuterFaces t)) (discrete.map (ordinaryOuterFaces t).ι)
    hfactor
  rw [← discrete.map_comp, spineToOuterFaces_ι]
  exact hspine (t + 2)

#print axioms outerFace_weak

end

end DaggerModels.PartII.OrdinarySpineModelOuterFaces
