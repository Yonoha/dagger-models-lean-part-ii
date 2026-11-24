import DaggerModelsPartII.JTCylinderMappingSpan
import DaggerModelsPartII.JTCylinderReedy
import DaggerModelsPartII.JTCEJoyalAugmentation
import DaggerModelsPartII.StrictFrameMappingWeak
import ActualRightConeFinalEdgeWeak

/-!
# Exact weak transport through the original cylinder Hom span

The literal cylinder augmentation weakness and original cone under-Reedy
condition remain explicit inputs. With those two geometric inputs, the
checked frame maps induce Kan weak maps on literal Hom, and their exact
target naturality transfers the chosen cone unit weakness to actual CE.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.JTCylinderMappingWeak

open JTXiEndpointCollapse JTCylinderMappingSpan

noncomputable section

private def ordinaryJoyalModel : ModelCategory SSet.{0} :=
  DaggerActualDCHRightInducedAndMainTheoremD.ordinaryJoyalModel.{0}

private local instance : ModelCategory SSet.{0} := ordinaryJoyalModel
private local instance : ModelCategory (Under boundary) :=
  JTEndpointCobase.underModel boundary
private local instance : ModelCategory (Under boundary)ᵒᵖ := inferInstance
private local instance : ModelCategory (SimplexCategoryᵒᵖ ⥤ (Under boundary)ᵒᵖ) :=
  simplicialReedyModelCategory (Under boundary)ᵒᵖ

private theorem under_weak_of_native {X Y : Under boundary} (f : X ⟶ Y)
    (hf : DaggerNativeJoyalMappingTest.weakCategoricalEquivalences f.right) :
    weakEquivalences (Under boundary) f := by
  let M := DaggerNativeOriginalJoyalSmithModelData.modelData.model
  change M.categoryWithWeakEquivalences.weakEquivalences f.right
  dsimp only [M]
  rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelWeak]
  exact hf

/-- The actual cylinder-to-CE map is original Joyal weak when the
specified cylinder augmentation is original Joyal weak. -/
theorem toCE_weak
    (hCyl : ∀ k : SimplexCategory,
      DaggerNativeJoyalMappingTest.weakCategoricalEquivalences
        (JTCylinderFrame.augmentation.app k)) (k : SimplexCategory) :
    DaggerNativeJoyalMappingTest.weakCategoricalEquivalences
      (JTCylinderCEComparison.valueComparison.app k) := by
  apply DaggerNativeJoyalMappingTest.weakCategoricalEquivalences.of_postcomp
    _ (JTCEAugmentation.CEAugmentation.app k)
      (JTCEJoyalAugmentation.CEAugmentation_weak k)
  rw [show JTCylinderCEComparison.valueComparison.app k ≫
      JTCEAugmentation.CEAugmentation.app k = JTCylinderFrame.augmentation.app k from
    NatTrans.congr_app JTCylinderCEComparison.valueComparison_augmentation k]
  exact hCyl k

/-- The same original Joyal input makes the actual cylinder-to-original
cone map weak, using its literal augmentation equation. -/
theorem toCone_weak
    (hCyl : ∀ k : SimplexCategory,
      DaggerNativeJoyalMappingTest.weakCategoricalEquivalences
        (JTCylinderFrame.augmentation.app k)) (k : SimplexCategory) :
    DaggerNativeJoyalMappingTest.weakCategoricalEquivalences
      (JTCylinderConeComparison.comparison.app k) := by
  apply DaggerNativeJoyalMappingTest.weakCategoricalEquivalences.of_postcomp
    _ (DaggerActualRightConeFinalEdgeMaps.projection k.len)
      (DaggerActualRightConeFinalEdgeWeak.projection_categorical_weak k.len)
  rw [JTCylinderConeComparison.comparison_augmentation]
  exact hCyl k

/-- The literal CE Hom restriction is Kan weak under the actual
cylinder augmentation input and original Joyal target fibrancy. -/
theorem fromCE_GW (Z : Under boundary) [IsFibrant Z]
    (hCyl : ∀ k : SimplexCategory,
      DaggerNativeJoyalMappingTest.weakCategoricalEquivalences
        (JTCylinderFrame.augmentation.app k)) :
    DaggerSSetGluing.GW (fromCE Z) := by
  letI : IsFibrant JTCylinderFrame.under.op := JTCylinderReedy.under_op_isFibrant
  letI : IsFibrant (Under.lift CE CE_boundary).op :=
    JTCEJoyalResolution.ceUnder_op_isFibrant
  have hg : weakEquivalences (SimplexCategoryᵒᵖ ⥤ (Under boundary)ᵒᵖ)
      (NatTrans.op JTCylinderCEComparison.underComparison) := by
    intro q
    rw [weakEquivalences_op]
    exact under_weak_of_native _ (toCE_weak hCyl q.unop)
  letI : ModelCategory SSet.{0} := SSet.modelCategoryQuillen.inst
  have h : weakEquivalences SSet.{0} (fromCE Z) :=
    StrictFrameMappingWeak.strictMapping_map_weak Z
      (NatTrans.op JTCylinderCEComparison.underComparison) hg
  exact (DaggerSSetGluing.weakEquivalence_iff_GW _).1
    ((weakEquivalence_iff _).2 h)

/-- The literal original cone Hom restriction is Kan weak under the
same augmentation input and the explicit original cone Reedy condition. -/
theorem fromCone_GW (Z : Under boundary) [IsFibrant Z]
    (hCyl : ∀ k : SimplexCategory,
      DaggerNativeJoyalMappingTest.weakCategoricalEquivalences
        (JTCylinderFrame.augmentation.app k))
    (hCone : IsFibrant JTCylinderConeComparison.coneUnder.op) :
    DaggerSSetGluing.GW (fromCone Z) := by
  letI : IsFibrant JTCylinderFrame.under.op := JTCylinderReedy.under_op_isFibrant
  letI : IsFibrant JTCylinderConeComparison.coneUnder.op := hCone
  have hg : weakEquivalences (SimplexCategoryᵒᵖ ⥤ (Under boundary)ᵒᵖ)
      (NatTrans.op JTCylinderConeComparison.comparisonUnder) := by
    intro q
    rw [weakEquivalences_op]
    exact under_weak_of_native _ (toCone_weak hCyl q.unop)
  letI : ModelCategory SSet.{0} := SSet.modelCategoryQuillen.inst
  have h : weakEquivalences SSet.{0} (fromCone Z) :=
    StrictFrameMappingWeak.strictMapping_map_weak Z
      (NatTrans.op JTCylinderConeComparison.comparisonUnder) hg
  exact (DaggerSSetGluing.weakEquivalence_iff_GW _).1
    ((weakEquivalence_iff _).2 h)

open JTStrictificationCoefficients JTChosenOrdinaryAdjoint JTChosenCEUnitBoundary

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

/-- The exact chosen unit on actual CE Hom is Kan weak once the two
specified geometric frame inputs hold. No ordinary Joyal unit premise enters. -/
theorem etaCE_GW_of_frame_inputs
    (hCyl : ∀ k : SimplexCategory,
      DaggerNativeJoyalMappingTest.weakCategoricalEquivalences
        (JTCylinderFrame.augmentation.app k))
    (hCone : IsFibrant JTCylinderConeComparison.coneUnder.op)
    (W : Source) (x y : (chosenT W).toSSet.obj (op ⦋0⦌)) :
    DaggerSSetGluing.GW (JTCEPlainMappingTarget.plainCEHomMap (etaUnder W x y)) := by
  let S : Under JTXiEndpointCollapse.boundary := sourceUnder W x y
  let T : Under JTXiEndpointCollapse.boundary := targetUnder W x y
  have hS : IsFibrant S := sourceUnder_fibrant W x y
  have hT : IsFibrant T := targetUnder_fibrant W x y
  have hCX := @fromCone_GW S hS hCyl hCone
  have hCY := @fromCone_GW T hT hCyl hCone
  have hEX := @fromCE_GW S hS hCyl
  have hEY := @fromCE_GW T hT hCyl
  letI : ModelCategory SSet.{0} := SSet.modelCategoryQuillen.inst
  haveI : WeakEquivalence (fromCone (sourceUnder W x y)) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).2 hCX
  haveI : WeakEquivalence (fromCone (targetUnder W x y)) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).2 hCY
  haveI : WeakEquivalence
      (postcompose JTCylinderConeComparison.coneUnder (etaUnder W x y)) :=
    etaCone_weak W x y
  haveI : WeakEquivalence (postcompose JTCylinderFrame.under (etaUnder W x y)) :=
    weakEquivalence_of_precomp_of_fac (fromCone_naturality (etaUnder W x y)).symm
  haveI : WeakEquivalence (fromCE (sourceUnder W x y)) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).2 hEX
  haveI : WeakEquivalence (fromCE (targetUnder W x y)) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).2 hEY
  exact (DaggerSSetGluing.weakEquivalence_iff_GW _).1
    (weakEquivalence_of_postcomp_of_fac (fromCE_naturality (etaUnder W x y)))

end

end DaggerModels.PartII.JTCylinderMappingWeak
