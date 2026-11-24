import DaggerModelsPartII.WeakFunctorReplacement
import DaggerModelsPartII.JTBarFunctorWeak
import DaggerModelsPartII.JTFrameQuillen
import DaggerModelsPartII.CofibrantLocalizingFamily

/-!
# Frame realization of arbitrary cofibrant replacements of constant diagrams

The exact bar augmentation and its proven weak frame image transport to every
weak augmentation with cofibrant source. In particular, any cofibrant arrow
resolution of delta applied to an original dagger Joyal weak map has weak
frame image. There is no cofibrancy assumption on either constant diagram.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra DaggerModels

namespace DaggerModels.PartII.JTCofibrantAugmentationWeak

open SegalLocalizers ConstantVertexAdjunction JTProjectiveBar JTFrameAdjunction
open OrdinaryRigidification.DaggerRigidification

noncomputable section

private local instance : ModelCategory ReverseDaggerSpace.{0} :=
  ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
private local instance : ModelCategory DaggerSimplicialCat.{0, 0} :=
  DaggerActualRigidificationQuillen.modelG.{0}

private theorem frameRealization_trivialCofibration_weak
    {A B : ReverseDaggerSpace.{0}} (i : A ⟶ B)
    (hi : trivialCofibrations ReverseDaggerSpace.{0} i) :
    weakEquivalences DaggerSimplicialCat.{0, 0} (frameRealization.map i) := by
  letI : adjunction.IsQuillenAdjunction := JTFrameQuillen.isQuillenAdjunction
  letI : frameRealization.PreservesTrivialCofibrations :=
    Adjunction.IsQuillenAdjunction.preservesTrivialCofibrations adjunction
  exact (Functor.PreservesTrivialCofibrations.trivialCofibrations_le
    frameRealization i hi).2

/-- Any original projective weak augmentation into delta X has weak frame
image when its source is projectively cofibrant. -/
theorem frameRealization_augmentation_weak (X : DaggerSSet.{0})
    {Q : ReverseDaggerSpace.{0}} [IsCofibrant Q] (q : Q ⟶ delta.obj X)
    (hq : weakEquivalences ReverseDaggerSpace.{0} q) :
    weakEquivalences DaggerSimplicialCat.{0, 0} (frameRealization.map q) := by
  letI : IsCofibrant (barOnDagger.obj X) :=
    JTBarProjectiveCofibrancy.barOnDagger_isCofibrant X
  exact WeakFunctorReplacement.map_weak_of_cofibrant_augmentation
    frameRealization (weakEquivalences DaggerSimplicialCat.{0, 0})
    frameRealization_trivialCofibration_weak (barAugmentation.app X)
    (JTBarProjectiveCofibrancy.barAugmentation_weak X)
    (JTBarDensityWeak.frameRealization_barAugmentation_weak X) q hq

/-- Every cofibrant arrow resolution of the literal delta image of an
original dagger Joyal weak equivalence has weak actual frame realization. -/
theorem frameRealization_resolution_weak {X Y : DaggerSSet.{0}} (f : X ⟶ Y)
    (hf : DaggerJoyalWeakProperties.standardJoyalWeakEquivalences f)
    (R : CofibrantArrowResolution (delta.map f)) :
    weakEquivalences DaggerSimplicialCat.{0, 0} (frameRealization.map R.hom) := by
  let P := weakEquivalences DaggerSimplicialCat.{0, 0}
  letI hsource : IsCofibrant R.source := R.source_cofibrant
  letI htarget : IsCofibrant R.target := R.target_cofibrant
  have hleft : P (frameRealization.map R.comparison.left) :=
    frameRealization_augmentation_weak X (Q := R.source) R.comparison.left
      ((weakEquivalence_iff _).1 R.source_weak)
  have hright : P (frameRealization.map R.comparison.right) :=
    frameRealization_augmentation_weak Y (Q := R.target) R.comparison.right
      ((weakEquivalence_iff _).1 R.target_weak)
  have hC : P (daggerRigidification.map f) := by
    change weakEquivalences DaggerSimplicialCat.{0, 0} _
    rw [DaggerActualRigidificationQuillen.target_weak]
    exact hf
  let ea : Arrow.mk (frameRealization.map (delta.map f)) ≅
      Arrow.mk (daggerRigidification.map f) :=
    Arrow.isoMk (JTStrictTransport.Theta.app X) (JTStrictTransport.Theta.app Y)
      (JTStrictTransport.Theta.hom.naturality f).symm
  have hdelta : P (frameRealization.map (delta.map f)) :=
    (P.arrow_mk_iso_iff ea).2 hC
  apply P.of_postcomp _ (frameRealization.map R.comparison.right) hright
  have hw : R.hom ≫ R.comparison.right = R.comparison.left ≫ delta.map f := by
    simpa only [Functor.id_map] using R.comparison.w.symm
  rw [← frameRealization.map_comp, hw, frameRealization.map_comp]
  exact P.comp_mem _ _ hleft hdelta

end

end DaggerModels.PartII.JTCofibrantAugmentationWeak
