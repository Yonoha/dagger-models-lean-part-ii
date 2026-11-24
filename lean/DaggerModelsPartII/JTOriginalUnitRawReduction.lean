import DaggerModelsPartII.JTRawOrdinaryAdjoint
import NativeAllCofibrantLocalizationSaturation

/-!
# The original chosen JT unit reduced to its actual raw action

The exact localized square and the two already weak vertical actions show
that weakness of the original chosen gTilde action is equivalent to weakness
of the actual raw transpose action at the projective image vertices.
The remaining raw action is an explicit premise, not a new proof of weakness.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTOriginalUnitRawReduction

noncomputable section

private theorem weak_iff_of_localized_square {A B C D : SSet.{0}}
    (f : A ⟶ B) (g : B ⟶ D) (p : A ⟶ C) (h : C ⟶ D)
    [WeakEquivalence g] [WeakEquivalence p]
    (hs : (weakEquivalences SSet.{0}).Q.map f ≫
        (weakEquivalences SSet.{0}).Q.map g =
      (weakEquivalences SSet.{0}).Q.map p ≫
        (weakEquivalences SSet.{0}).Q.map h) :
    WeakEquivalence f ↔ WeakEquivalence h := by
  let Q := (weakEquivalences SSet.{0}).Q
  have : IsIso (Q.map g) :=
    Localization.inverts Q (weakEquivalences SSet.{0}) g (mem_weakEquivalences g)
  have : IsIso (Q.map p) :=
    Localization.inverts Q (weakEquivalences SSet.{0}) p (mem_weakEquivalences p)
  calc
    WeakEquivalence f ↔ IsIso (Q.map f) :=
      DaggerNativeAllCofibrantLocalizationSaturation.weakEquivalence_iff_localization_isIso Q f
    _ ↔ IsIso (Q.map f ≫ Q.map g) := (isIso_comp_right_iff _ _).symm
    _ ↔ IsIso (Q.map p ≫ Q.map h) := by rw [hs]
    _ ↔ IsIso (Q.map h) := isIso_comp_left_iff _ _
    _ ↔ WeakEquivalence h :=
      (DaggerNativeAllCofibrantLocalizationSaturation.weakEquivalence_iff_localization_isIso
        Q h).symm

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

/-- The original chosen gTilde action is weak exactly when the actual raw
transpose action at the same projective image pair is weak. -/
theorem original_chosenFiberMap_weak_iff_raw (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    WeakEquivalence (JTGtildeOrderedFiberAction.chosenFiberMap W x y) ↔
      WeakEquivalence (JTRawOrdinaryAdjoint.rawChosenFiberMapAtP W x y) := by
  have : WeakEquivalence
      (JTGeneralOrderedFiberWeak.chosenFiberMap (JTRawFreeInnerComparison.ell W).hom
        (JTGtildeOrderedFiberAction.targetVertices W x y).1
        (JTGtildeOrderedFiberAction.targetVertices W x y).2) :=
    JTRawFreeInnerOrderedFiber.ell_chosenFiberMap_weak W _ _
  have : WeakEquivalence (JTProjectiveOrderedFiberComparison.chosenFiberMap W x y) :=
    JTProjectiveOrderedFiberComparison.chosenFiberMap_weak W x y
  exact weak_iff_of_localized_square _ _ _ _
    (JTRawOrdinaryAdjoint.chosenFiberMap_localized_square W x y)

/-- A proof of weakness for that same raw action proves weakness of the
ORIGINAL chosen gTilde action, without replacing its source or target. -/
theorem original_chosenFiberMap_weak_of_raw (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌))
    (hraw : WeakEquivalence (JTRawOrdinaryAdjoint.rawChosenFiberMapAtP W x y)) :
    WeakEquivalence (JTGtildeOrderedFiberAction.chosenFiberMap W x y) :=
  (original_chosenFiberMap_weak_iff_raw W x y).2 hraw

end

end DaggerModels.PartII.JTOriginalUnitRawReduction
