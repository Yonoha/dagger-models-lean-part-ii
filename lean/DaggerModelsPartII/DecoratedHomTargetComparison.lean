import DaggerModelsPartII.DecoratedHomLocalizedCocone
import ActualNecklaceFlagAugmentation
import NativeAllCofibrantLocalizationSaturation

/-!
# The actual decorated evaluator compared with the original target necklace nerve

The target bar and both its weak maps are the retained original Part I maps.
The source map is built from the ACTUAL decorated evaluator and its weak
projection. Its invertibility is equivalent to weakness of that evaluator;
invertibility is not assumed or proved here.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace
open DaggerNativeSimplicialReplacement
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.DecoratedHomTargetComparison

open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Q := (weakEquivalences SSet.{0}).Q
private abbrev R (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev v (W : Source) (x : (row W ⦋0⦌).obj (op ⦋0⦌)) :=
  JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x

variable (W : Source) (x y : (row W ⦋0⦌).obj (op ⦋0⦌))

/-- The original necklace-over-raw-realization index at the SAME raw vertices. -/
abbrev TargetIndex := NecklacesOver (R W) (v W x) (v W y)

/-- The exact original Part I whole flag-weighted replacement. -/
def targetBar : SSet.{0} := DaggerBisimplicialDiagonal.diag
  (replacement (NecklacesOver.flagDiagram (R W) (v W x) (v W y)))

/-- The original flag augmentation followed by the exact original-Hom iso. -/
def targetAugmentation : targetBar W x y ⟶ DecoratedNecklaceHomDiagram.rawHom W x y :=
  diagonalAugmentation (NecklacesOver.flagDiagram (R W) (v W x) (v W y))
    (DaggerActualNecklaceFlagAugmentation.augmentation (R W) (v W x) (v W y)) ≫
      (flagOriginalHomIso (R W) (v W x) (v W y)).hom

/-- The retained original target augmentation is weak without W fibrancy. -/
theorem targetAugmentation_weak : WeakEquivalence (targetAugmentation W x y) := by
  have : WeakEquivalence
      (diagonalAugmentation (NecklacesOver.flagDiagram (R W) (v W x) (v W y))
        (DaggerActualNecklaceFlagAugmentation.augmentation (R W) (v W x) (v W y))) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
      (DaggerActualNecklaceFlagAugmentation.augmentation_GW (R W) (v W x) (v W y))
  dsimp only [targetAugmentation]
  infer_instance

/-- The original full-chain target projection, retaining the target necklace index. -/
def targetProjection : targetBar W x y ⟶ nerve (TargetIndex W x y) :=
  diagonalProjection (NecklacesOver.flagDiagram (R W) (v W x) (v W y))

theorem targetProjection_weak : WeakEquivalence (targetProjection W x y) :=
  (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
    (DaggerActualNecklaceFlagAugmentation.projection_GW (R W) (v W x) (v W y))

private def weakIso {X Y : SSet.{0}} (f : X ⟶ Y) (hf : WeakEquivalence f) :
    Q.obj X ≅ Q.obj Y := by
  have : WeakEquivalence f := hf
  have : IsIso (Q.map f) := Localization.inverts Q (weakEquivalences SSet.{0}) f
    (mem_weakEquivalences f)
  exact asIso (Q.map f)

/-- The exact original target-bar span identifies SAME raw Hom and target nerve. -/
def targetNerveIso : Q.obj (DecoratedNecklaceHomDiagram.rawHom W x y) ≅
    Q.obj (nerve (TargetIndex W x y)) :=
  (weakIso (targetAugmentation W x y) (targetAugmentation_weak W x y)).symm ≪≫
    weakIso (targetProjection W x y) (targetProjection_weak W x y)

/-- The ACTUAL evaluator induces this map from the SAME decorated source nerve. -/
def indexEvaluator :
    Q.obj (nerve (DecoratedNecklaceHomDiagram.Index W x y)) ⟶
      Q.obj (DecoratedNecklaceHomDiagram.rawHom W x y) :=
  (weakIso (DecoratedNecklaceHomBar.cylinderProjection W x y)
      (DecoratedNecklaceHomBar.cylinderProjection_weak W x y)).inv ≫
    Q.map (DecoratedNecklaceHomBar.evaluator W x y)

/-- Its pullback along the SAME cylinder projection is exactly the original evaluator. -/
theorem cylinder_evaluator_square :
    Q.map (DecoratedNecklaceHomBar.cylinderProjection W x y) ≫
        indexEvaluator W x y = Q.map (DecoratedNecklaceHomBar.evaluator W x y) := by
  let e := weakIso (DecoratedNecklaceHomBar.cylinderProjection W x y)
    (DecoratedNecklaceHomBar.cylinderProjection_weak W x y)
  change e.hom ≫ (e.inv ≫ _) = _
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- It agrees with the previously defined whole-bar localized evaluator. -/
theorem necklace_evaluator_square :
    Q.map (DecoratedNecklaceHomBar.necklaceProjection W x y) ≫
        indexEvaluator W x y = DecoratedNecklaceHomBar.localizedEvaluator W x y := by
  apply (cancel_epi (DecoratedNecklaceHomBar.leftBarIso W x y).hom).mp
  rw [← Category.assoc]
  change (Q.map (DecoratedNecklaceHomBar.leftBarMap W x y) ≫
    Q.map (DecoratedNecklaceHomBar.necklaceProjection W x y)) ≫ _ = _
  rw [← Q.map_comp, DecoratedNecklaceHomBar.projection_square, cylinder_evaluator_square]
  dsimp only [DecoratedNecklaceHomBar.localizedEvaluator]
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- A specified target comparison built from ACTUAL maps, not an arbitrary source iso. -/
def targetComparison : Q.obj (nerve (DecoratedNecklaceHomDiagram.Index W x y)) ⟶
    Q.obj (nerve (TargetIndex W x y)) :=
  indexEvaluator W x y ≫ (targetNerveIso W x y).hom

/-- Exactly the remaining target-map question; neither side is proved here. -/
theorem targetComparison_isIso_iff_evaluator_weak :
    IsIso (targetComparison W x y) ↔
      WeakEquivalence (DecoratedNecklaceHomBar.evaluator W x y) := by
  have : IsIso ((weakIso (DecoratedNecklaceHomBar.cylinderProjection W x y)
      (DecoratedNecklaceHomBar.cylinderProjection_weak W x y)).inv) := inferInstance
  calc
    IsIso (targetComparison W x y) ↔ IsIso (indexEvaluator W x y) :=
      isIso_comp_right_iff _ _
    _ ↔ IsIso (Q.map (DecoratedNecklaceHomBar.evaluator W x y)) :=
      isIso_comp_left_iff _ _
    _ ↔ WeakEquivalence (DecoratedNecklaceHomBar.evaluator W x y) :=
      (DaggerNativeAllCofibrantLocalizationSaturation.weakEquivalence_iff_localization_isIso
        Q _).symm

end

end DaggerModels.PartII.DecoratedHomTargetComparison
