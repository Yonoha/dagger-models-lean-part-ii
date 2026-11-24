import OrdinaryCSSCompletionExtension
import OrdinaryCSSFibrantOrderedRecognition
import OrdinaryCompletedUnitChosenMap

/-!
# CSS weakness on the original ordered fibers of a Segal source

The source is only injectively fibrant and Segal. Extend the same CSS weak
map through its actual trivial-cofibration completion unit. The extension is
weak between actual CSS fibrant objects, and the original unit is weak on
chosen ordered fibers. Existing localized chosen-map composition returns the
result to the original map with the original endpoints.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalCSSWeakOrderedRecognition

open OrdinaryCSSLocalization (Space)
open RawOrdinaryJTChosenMapCalibration (chosenMappingMap)

noncomputable section

private abbrev C := OrdinaryCSSLocalization.model
private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- A CSS weak original map from a fibrant Segal source into an actual CSS
fibrant target is weak on the same chosen ordered mapping fibers. -/
theorem cssWeak_chosenMappingMap_weak {W Z : Space} [IsFibrant W]
    (f : W ⟶ Z) (hSegal : OrdinaryCSSConditions.segalCondition W)
    (hZ : @IsFibrant Space _ C.categoryWithFibrations _ Z)
    (hf : C.categoryWithWeakEquivalences.weakEquivalences f)
    (x y : (W.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    WeakEquivalence (chosenMappingMap f x y) := by
  obtain ⟨g, hfac, hgCSS⟩ :=
    OrdinaryCSSCompletionExtension.exists_weak_extension hSegal hZ f hf
  let j := OrdinaryChosenCSSCompletion.unit W
  let Q := (weakEquivalences SSet.{0}).Q
  have hR := OrdinaryChosenCSSCompletion.completion_cssFibrant W hSegal
  have hj : WeakEquivalence (chosenMappingMap j x y) :=
    OrdinaryCompletedUnitChosenMap.completedUnitChosenMap_weak
      W hSegal (OrdinaryChosenCSSCompletion.completion W)
      (OrdinaryChosenCSSCompletion.inclusion W)
      (OrdinaryChosenCSSCompletion.inclusion_rowWeak W) x y
  have hg : WeakEquivalence (chosenMappingMap g
      ((j.app (op ⦋0⦌)).app (op ⦋0⦌) x)
      ((j.app (op ⦋0⦌)).app (op ⦋0⦌) y)) :=
    OrdinaryCSSFibrantOrderedRecognition.cssWeak_chosenMappingMap_weak
      g hR hZ hgCSS _ _
  have hc := OrdinaryCompletedUnitChosenMap.chosenMappingMap_comp j g x y
  haveI : IsIso (Q.map (chosenMappingMap j x y)) :=
    (DaggerNativeAllCofibrantLocalizationSaturation.weakEquivalence_iff_localization_isIso
      Q _).mp hj
  haveI : IsIso (Q.map (chosenMappingMap g
      ((j.app (op ⦋0⦌)).app (op ⦋0⦌) x)
      ((j.app (op ⦋0⦌)).app (op ⦋0⦌) y))) :=
    (DaggerNativeAllCofibrantLocalizationSaturation.weakEquivalence_iff_localization_isIso
      Q _).mp hg
  have hIso : IsIso (Q.map (chosenMappingMap (j ≫ g) x y)) := by
    rw [← hc]
    infer_instance
  have hw : WeakEquivalence (chosenMappingMap (j ≫ g) x y) :=
    (DaggerNativeAllCofibrantLocalizationSaturation.weakEquivalence_iff_localization_isIso
      Q _).mpr hIso
  change j ≫ g = f at hfac
  subst f
  exact hw

#print axioms cssWeak_chosenMappingMap_weak

end

end DaggerModels.PartII.OrdinarySegalCSSWeakOrderedRecognition
