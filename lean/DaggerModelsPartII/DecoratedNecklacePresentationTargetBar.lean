import DaggerModelsPartII.DecoratedNecklacePresentationHom
import ActualIteratedGadgetHomAugmentationWeakness
import ActualIteratedGadgetNecklaceComparison

/-!
# The presentation Hom bar maps to the unchanged original gadget Hom bar

The original internal native code and its complete map into the raw JT
realization are retained in the level-zero iterated-gadget index. The two
whole-bar augmentations agree at the SAME raw rigidification Hom. This
reduces evaluator weakness to the actual presentation target nerve map;
neither weakness is asserted unconditionally.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerModels.OrdinaryRigidification
open DaggerModels.OriginalOrdinaryMovingHomColimits
open DaggerChosenRigidificationNecklace
open DaggerNativeSimplicialReplacement
open DaggerNativeSimplicialReplacementWeightsChange
open DaggerNativeSimplicialReplacementReindex
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.DecoratedNecklacePresentationTargetBar

open JTProjectiveOrderedFiberComparison (row)
open DecoratedCylinderNecklacePresentation

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev R (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev v (W : Source) (x : (row W ⦋0⦌).obj (op ⦋0⦌)) :=
  JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x

variable (W : Source) (x y : (row W ⦋0⦌).obj (op ⦋0⦌))

/-- The SAME original iterated-gadget target index, reached through the
actual complete descended-necklace map and the checked original inclusion. -/
def gadgetFunctor : Presentation W x y ⥤
    DaggerActualIteratedGadgetData.Over (R W) (v W x) (v W y) :=
  toTarget W x y ⋙
    DaggerActualIteratedGadgetNecklaceComparison.inclusion
      (R W) (v W x) (v W y)

/-- The exact retained original gadget Hom-weight diagram. -/
private abbrev targetDiagram :=
  DaggerActualIteratedGadgetHomAugmentation.diagram (R W) (v W x) (v W y)

/-- Both weights are the original rigidification Hom of the SAME internal
native necklace, with the SAME morphism and endpoint transports. -/
def internalWeightIso : DecoratedNecklacePresentationHom.internalHomDiagram W x y ≅
    gadgetFunctor W x y ⋙ targetDiagram W x y :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro s t f
    rfl)

/-- The unchanged original iterated-gadget Hom bar of the raw realization. -/
def targetBar : SSet.{0} := DaggerBisimplicialDiagonal.diag
  (replacement (targetDiagram W x y))

/-- Change only the definitionally identical internal Hom weight, then
reindex each whole presentation chain by its actual target gadget. -/
def toTargetBar : DecoratedNecklacePresentationHom.internalBar W x y ⟶
    targetBar W x y :=
  diagonalChange (internalWeightIso W x y).hom ≫
    diagonalReindex (gadgetFunctor W x y) (targetDiagram W x y)

/-- The level-zero target gadget has exactly the original raw necklace map. -/
theorem target_obj_map (s : Presentation W x y) :
    ((gadgetFunctor W x y).obj s).map =
      s.fiber.hom.right ≫
        JTNecklaceEndpointCylinder.descend W x y
          (OrderedLabelElements.necklace W
            (OrderedNecklaceVertexPoints.boundaryPoint W x y) s.base)
          (OrderedLabelElements.degree W
            (OrderedNecklaceVertexPoints.boundaryPoint W x y) s.base)
          (OrderedLabelElements.label W
            (OrderedNecklaceVertexPoints.boundaryPoint W x y) s.base) :=
  toTarget_obj_map W x y s

/-- The original target gadget leg and the actual internal-cylinder evaluator
are identical at each complete internal native necklace Hom coefficient. -/
theorem target_leg_eq_internalRight (s : Presentation W x y) :
    (internalWeightIso W x y).hom.app s ≫
      (DaggerActualIteratedGadgetHomAugmentation.augmentation
        (R W) (v W x) (v W y)).app ((gadgetFunctor W x y).obj s) =
      (DecoratedNecklacePresentationHom.internalRight W x y).app s := by
  change (𝟙 _) ≫ castMap (rigidification.map (((gadgetFunctor W x y).obj s).map))
      _ _ _ _ _ _ =
    castMap (rigidification.map
      ((DecoratedNecklacePresentationHom.internalEvaluation W x y).app s))
      _ _ _ _ _ _ ≫
    castMap (rigidification.map
      (JTNecklaceEndpointCylinder.descend W x y
        (OrderedLabelElements.necklace W
          (OrderedNecklaceVertexPoints.boundaryPoint W x y) s.base)
        (OrderedLabelElements.degree W
          (OrderedNecklaceVertexPoints.boundaryPoint W x y) s.base)
        (OrderedLabelElements.label W
          (OrderedNecklaceVertexPoints.boundaryPoint W x y) s.base)))
      _ _ _ _ _ _
  rw [Category.id_comp]
  rw [← castMap_comp]
  refine castMap_congr ?_ _ _ _ _ _ _ _ _
  rw [← rigidification.map_comp, target_obj_map]
  rfl

/-- Both original entire-bar augmentations agree at the SAME raw Hom. -/
theorem target_augmentation_triangle :
    toTargetBar W x y ≫
      DaggerActualIteratedGadgetHomAugmentation.toOriginalHom (R W) (v W x) (v W y) =
      DecoratedNecklacePresentationHom.internalEvaluator W x y := by
  dsimp only [toTargetBar, DaggerActualIteratedGadgetHomAugmentation.toOriginalHom,
    DecoratedNecklacePresentationHom.internalEvaluator]
  rw [Category.assoc,
    DaggerNativeSimplicialReplacementReindex.augmentation_square]
  rw [DaggerNativeSimplicialReplacementWeightsChange.augmentation_square]
  apply congrArg (diagonalAugmentation
    (DecoratedNecklacePresentationHom.internalHomDiagram W x y))
  apply NatTrans.ext
  funext s
  exact target_leg_eq_internalRight W x y s

/-- The original raw-Hom evaluator agrees with the original gadget augmentation
after two actual whole-bar maps. No inverse is chosen at the point-set level. -/
theorem evaluator_target_square :
    DecoratedNecklacePresentationHom.toCylinderBar W x y ≫
      DecoratedNecklaceHomBar.evaluator W x y =
    toTargetBar W x y ≫
      DaggerActualIteratedGadgetHomAugmentation.toOriginalHom
        (R W) (v W x) (v W y) := by
  rw [DecoratedNecklacePresentationHom.evaluator_triangle,
    target_augmentation_triangle]

/-- The whole target-weight isomorphism is Kan weak on the entire replacement. -/
private theorem weightBar_weak :
    WeakEquivalence (diagonalChange (internalWeightIso W x y).hom) :=
  OrderedLabelNaturalWeakSpans.diagonalChange_weak _ (fun _ ↦ inferInstance)

/-- The target reindexing is weak exactly when the ACTUAL target gadget nerve
map is weak; every original gadget Hom weight is already contractible. -/
theorem reindex_weak_iff_nerve :
    WeakEquivalence (diagonalReindex (gadgetFunctor W x y) (targetDiagram W x y)) ↔
      WeakEquivalence (nerveMap (gadgetFunctor W x y)) := by
  have ht : WeakEquivalence (diagonalProjection (targetDiagram W x y)) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
      (DaggerActualIteratedGadgetHomAugmentation.projection_GW
        (R W) (v W x) (v W y))
  have hs : WeakEquivalence
      (diagonalProjection (gadgetFunctor W x y ⋙ targetDiagram W x y)) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
      (diagonalProjection_GW (gadgetFunctor W x y ⋙ targetDiagram W x y)
        (fun s ↦ DaggerActualIteratedGadgetHomAugmentation.diagram_point_GW
          (R W) (v W x) (v W y) ((gadgetFunctor W x y).obj s)))
  letI : WeakEquivalence (diagonalProjection (targetDiagram W x y)) := ht
  letI : WeakEquivalence
      (diagonalProjection (gadgetFunctor W x y ⋙ targetDiagram W x y)) := hs
  calc
    WeakEquivalence (diagonalReindex (gadgetFunctor W x y) (targetDiagram W x y)) ↔
        WeakEquivalence (diagonalReindex (gadgetFunctor W x y)
          (targetDiagram W x y) ≫ diagonalProjection (targetDiagram W x y)) :=
      (weakEquivalence_postcomp_iff _ _).symm
    _ ↔ WeakEquivalence
        (diagonalProjection (gadgetFunctor W x y ⋙ targetDiagram W x y) ≫
          nerveMap (gadgetFunctor W x y)) := by
      rw [DaggerNativeSimplicialReplacementReindex.projection_square]
    _ ↔ WeakEquivalence (nerveMap (gadgetFunctor W x y)) :=
      weakEquivalence_precomp_iff _ _

/-- Weakness of the full presentation-to-original-gadget bar is exactly
weakness of the original target gadget index map. -/
theorem toTargetBar_weak_iff_nerve :
    WeakEquivalence (toTargetBar W x y) ↔
      WeakEquivalence (nerveMap (gadgetFunctor W x y)) := by
  have hw : WeakEquivalence (diagonalChange (internalWeightIso W x y).hom) :=
    weightBar_weak W x y
  letI : WeakEquivalence (diagonalChange (internalWeightIso W x y).hom) := hw
  change WeakEquivalence (diagonalChange (internalWeightIso W x y).hom ≫
    diagonalReindex (gadgetFunctor W x y) (targetDiagram W x y)) ↔ _
  exact (weakEquivalence_precomp_iff _ _).trans (reindex_weak_iff_nerve W x y)

/-- The ACTUAL original decorated evaluator is weak exactly when the
presentation-to-original-gadget nerve map is weak. This is a criterion, not
a proof of either side. -/
theorem evaluator_weak_iff_target_nerve :
    WeakEquivalence (DecoratedNecklaceHomBar.evaluator W x y) ↔
      WeakEquivalence (nerveMap (gadgetFunctor W x y)) := by
  have hc : WeakEquivalence (DecoratedNecklacePresentationHom.toCylinderBar W x y) :=
    DecoratedNecklacePresentationHom.toCylinderBar_weak W x y
  have ht : WeakEquivalence
      (DaggerActualIteratedGadgetHomAugmentation.toOriginalHom
        (R W) (v W x) (v W y)) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
      (DaggerActualIteratedGadgetHomAugmentationWeakness.toOriginalHom_GW
        (R W) (v W x) (v W y))
  letI : WeakEquivalence (DecoratedNecklacePresentationHom.toCylinderBar W x y) := hc
  letI : WeakEquivalence
      (DaggerActualIteratedGadgetHomAugmentation.toOriginalHom
        (R W) (v W x) (v W y)) := ht
  calc
    WeakEquivalence (DecoratedNecklaceHomBar.evaluator W x y) ↔
        WeakEquivalence (DecoratedNecklacePresentationHom.toCylinderBar W x y ≫
          DecoratedNecklaceHomBar.evaluator W x y) :=
      (weakEquivalence_precomp_iff _ _).symm
    _ ↔ WeakEquivalence (toTargetBar W x y ≫
        DaggerActualIteratedGadgetHomAugmentation.toOriginalHom
          (R W) (v W x) (v W y)) := by rw [evaluator_target_square]
    _ ↔ WeakEquivalence (toTargetBar W x y) :=
      weakEquivalence_postcomp_iff _ _
    _ ↔ WeakEquivalence (nerveMap (gadgetFunctor W x y)) :=
      toTargetBar_weak_iff_nerve W x y

/-- The retained original necklace inclusion is weak, so the criterion concerns
the SAME actual target-necklace functor before localization. -/
theorem gadget_nerve_weak_iff_original_target_nerve :
    WeakEquivalence (nerveMap (gadgetFunctor W x y)) ↔
      WeakEquivalence (nerveMap (toTarget W x y)) := by
  have : WeakEquivalence (nerveMap
      (DaggerActualIteratedGadgetNecklaceComparison.inclusion
        (R W) (v W x) (v W y))) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
      (DaggerActualIteratedGadgetNecklaceComparison.inclusion_GW
        (R W) (v W x) (v W y))
  have h : nerveMap (gadgetFunctor W x y) = nerveMap (toTarget W x y) ≫
      nerveMap (DaggerActualIteratedGadgetNecklaceComparison.inclusion
        (R W) (v W x) (v W y)) :=
    nerveFunctor.map_comp (toTarget W x y).toCatHom
      (DaggerActualIteratedGadgetNecklaceComparison.inclusion
        (R W) (v W x) (v W y)).toCatHom
  rw [h]
  exact weakEquivalence_postcomp_iff _ _

/-- The ACTUAL evaluator is weak exactly when the SAME concrete functor to
original raw-target necklaces has weak nerve. Neither conclusion is proved. -/
theorem evaluator_weak_iff_original_target_nerve :
    WeakEquivalence (DecoratedNecklaceHomBar.evaluator W x y) ↔
      WeakEquivalence (nerveMap (toTarget W x y)) :=
  (evaluator_weak_iff_target_nerve W x y).trans
    (gadget_nerve_weak_iff_original_target_nerve W x y)

end

end DaggerModels.PartII.DecoratedNecklacePresentationTargetBar
