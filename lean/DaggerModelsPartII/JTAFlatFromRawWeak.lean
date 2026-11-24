import DaggerModelsPartII.JTOriginalUnitRawReduction
import DaggerModelsPartII.JTVarthetaChosenFiberWeak
import NativeAllCofibrantLocalizationSaturation

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra Opposite Simplicial DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTAFlatFromRawWeak

open JTAFlatOrderedFiberAction JTStrictificationCoefficients
open JTGtildeOrderedFiberAction JTChosenCEUnitBoundary

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

/-- Weakness of the actual raw ordered-fiber transpose transfers to the
literal chosen `aFlat` ordered-fiber map. -/
theorem chosenFiberMap_weak_of_raw (W : Source)
    (x y : (JTGtildeOrderedFiberAction.sourceRow W ⦋0⦌).obj (op ⦋0⦌))
    (hraw : WeakEquivalence (JTRawOrdinaryAdjoint.rawChosenFiberMapAtP W x y)) :
    WeakEquivalence (JTAFlatOrderedFiberAction.chosenFiberMap W x y) := by
  let Q := (weakEquivalences SSet.{0}).Q
  have hg : WeakEquivalence (JTGtildeOrderedFiberAction.chosenFiberMap W x y) :=
    JTOriginalUnitRawReduction.original_chosenFiberMap_weak_of_raw W x y hraw
  have hη : WeakEquivalence
      (JTEtaChosenFiber.etaChosenFiberMap W
        (targetVertices W x y).1 (targetVertices W x y).2) :=
    JTEtaChosenFiber.etaChosenFiberMap_weak W _ _
  have hϑ : WeakEquivalence
      (JTAFlatOrderedFiberAction.comparisonChosenMap W
        (chosenVertices W (targetVertices W x y).1
          (targetVertices W x y).2).1
        (chosenVertices W (targetVertices W x y).1
          (targetVertices W x y).2).2) :=
    JTVarthetaChosenFiberWeak.comparisonChosenMap_weak W _ _
  haveI : IsIso (Q.map
      (JTGtildeOrderedFiberAction.chosenFiberMap W x y)) :=
    Localization.inverts Q (weakEquivalences SSet.{0}) _ (mem_weakEquivalences _)
  haveI : IsIso (Q.map
      (JTEtaChosenFiber.etaChosenFiberMap W
        (targetVertices W x y).1 (targetVertices W x y).2)) :=
    Localization.inverts Q (weakEquivalences SSet.{0}) _ (mem_weakEquivalences _)
  haveI : IsIso (Q.map
      (JTAFlatOrderedFiberAction.comparisonChosenMap W
        (chosenVertices W (targetVertices W x y).1
          (targetVertices W x y).2).1
        (chosenVertices W (targetVertices W x y).1
          (targetVertices W x y).2).2)) :=
    Localization.inverts Q (weakEquivalences SSet.{0}) _ (mem_weakEquivalences _)
  have hcomp : IsIso (Q.map (JTAFlatOrderedFiberAction.chosenFiberMap W x y) ≫
      Q.map (JTAFlatOrderedFiberAction.comparisonChosenMap W
        (chosenVertices W (targetVertices W x y).1
          (targetVertices W x y).2).1
        (chosenVertices W (targetVertices W x y).1
          (targetVertices W x y).2).2)) := by
    rw [JTAFlatOrderedFiberAction.chosenFiberMap_localized_square W x y]
    infer_instance
  have hi : IsIso (Q.map (JTAFlatOrderedFiberAction.chosenFiberMap W x y)) :=
    (isIso_comp_right_iff _ _).1 hcomp
  exact (DaggerNativeAllCofibrantLocalizationSaturation.weakEquivalence_iff_localization_isIso
    Q (JTAFlatOrderedFiberAction.chosenFiberMap W x y)).2 hi

end

end DaggerModels.PartII.JTAFlatFromRawWeak
