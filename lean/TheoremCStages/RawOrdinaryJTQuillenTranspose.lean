import OrdinaryJTReedyQuillen
import OrdinaryJTCurriedTranspose
import RawOrdinaryJTRightNerve
import NativeInnerJoyalMappingWeak

/-!
# The actual raw unit in the curried ordinary JT Quillen adjunction

The raw free-inner comparison is retained without replacing its source,
target, or transpose. Its realization-side map is an original Joyal weak
equivalence into the original quasicategory target; its curried transpose
is exactly the curry of `gRawTilde`. These facts do not prove that the
transpose itself is weak in a CSS localization or on ordered fibers.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.RawOrdinaryJTQuillenTranspose

open OrdinaryJTCurriedAdjunction
open OrdinaryJTProjectiveQuillen (joyalModel)
open OrdinaryJTReedyQuillen (diagramModel)
open OrdinaryJTRealization JTReversalInput JTRawFreeInnerComparison

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

/-- The literal original raw input, with its two indices curried. -/
def input (W : Source) : SimplexCategoryᵒᵖ ⥤ SSet.{0} :=
  JTRealizationDiagonal.ordinaryCurry.obj (ordinaryInput.obj W)

/-- The original raw comparison, precomposed only with the currying unit isomorphism. -/
def leftComparison (W : Source) : left.obj (input W) ⟶ (rawTarget W).toSSet :=
  realization.map (curryEquivalence.unitIso.inv.app (ordinaryInput.obj W)) ≫ (rawG W).hom

/-- This is exactly the actual original raw transpose after currying. -/
theorem transpose_eq (W : Source) :
    (adjunction.homEquiv (input W) (rawTarget W).toSSet) (leftComparison W) =
      JTRealizationDiagonal.ordinaryCurry.map (JTRawOrdinaryAdjoint.gRawTilde W) :=
  OrdinaryJTCurriedTranspose.realization_transpose_curry
    (ordinaryInput.obj W) (rawTarget W).toSSet (rawG W).hom

/-- The actual realization-side comparison is weak in the original Joyal model. -/
theorem leftComparison_weak (W : Source) :
    joyalModel.categoryWithWeakEquivalences.weakEquivalences (leftComparison W) := by
  have hraw : joyalModel.categoryWithWeakEquivalences.weakEquivalences (rawG W).hom := by
    have he := DaggerNativeOriginalJoyalSmithModelData.modelData.modelWeak
    change joyalModel.categoryWithWeakEquivalences.weakEquivalences =
      DaggerNativeJoyalMappingTest.weakCategoricalEquivalences at he
    rw [he]
    exact DaggerNativeInnerJoyalMappingWeak.innerAnodyne_weak _
      (JTFreeInnerUnderlying.unit_underlying_innerAnodyne
        (DaggerJTRealization.daggerRealization.obj W))
  letI : ModelCategory SSet.{0} := joyalModel
  letI : CategoryWithCofibrations SSet.{0} := joyalModel.categoryWithCofibrations
  letI : CategoryWithFibrations SSet.{0} := joyalModel.categoryWithFibrations
  letI : CategoryWithWeakEquivalences SSet.{0} :=
    joyalModel.categoryWithWeakEquivalences
  letI : WeakEquivalence (rawG W).hom := (weakEquivalence_iff _).mpr hraw
  change weakEquivalences SSet.{0}
    (realization.map (curryEquivalence.unitIso.inv.app (ordinaryInput.obj W)) ≫ (rawG W).hom)
  have hiso : weakEquivalences SSet.{0}
      (realization.map (curryEquivalence.unitIso.inv.app (ordinaryInput.obj W))) :=
    (weakEquivalence_iff _).mp inferInstance
  exact (weakEquivalences SSet.{0}).comp_mem _ _ hiso hraw

/-- The right-nerve diagram at the actual raw target is Kan Reedy fibrant. -/
theorem target_reedyFibrant (W : Source) :
    @IsFibrant (SimplexCategoryᵒᵖ ⥤ SSet.{0}) _
      diagramModel.categoryWithFibrations _ (right.obj (rawTarget W).toSSet) := by
  letI := RawOrdinaryJTRightNerve.rawTarget_quasicategory W
  exact right_obj_reedyFibrant _

#print axioms transpose_eq
#print axioms leftComparison_weak
#print axioms target_reedyFibrant

end

end DaggerModels.PartII.RawOrdinaryJTQuillenTranspose
