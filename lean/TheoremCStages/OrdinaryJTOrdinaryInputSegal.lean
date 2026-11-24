import OrdinaryFreeRestrictionCalibration
import OrdinaryCSSConditions
import DaggerModelsPartII.SegalSpaceConditions
import TopCatModelCategory.ModelCategorySSet

/-!
# Ordinary spine tests of the literal JT input

The arbitrary-source free-restriction mapping isomorphism transports
each original free dagger spine test to the ordinary horizontal spine
test of the same reversal diagram. This does not impose or infer the
ordinary walking-isomorphism completeness condition.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryJTOrdinaryInputSegal

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

/-- The original dagger Segal tests imply the strict ordinary spine tests
of the literal uncurried and re-curried ordinaryInput. No ordinary
completeness conclusion is included. -/
theorem ordinaryInput_segalCondition (W : Source)
    (hW : SegalLocalizers.segalCondition W) :
    OrdinaryCSSConditions.segalCondition
      (JTRealizationDiagonal.ordinaryCurry.obj
        (JTReversalInput.ordinaryInput.obj W)) := by
  intro n hn
  let i := (DaggerNativeStandardSpineInner.spine n).ι
  let eT := OrdinaryFreeRestrictionEnriched.freeDiscreteMappingIso
    (Δ[n] : SSet.{0}) W
  let eS := OrdinaryFreeRestrictionEnriched.freeDiscreteMappingIso
    (DaggerNativeStandardSpineInner.spine n).toSSet W
  have hnat := OrdinaryFreeRestrictionCalibration.freeDiscreteMappingIso_natural
    i W
  change
    diagramMappingPrecomp (OrdinaryCSSLocalization.spineMap n)
        (JTRealizationDiagonal.ordinaryCurry.obj
          (JTReversalInput.ordinaryInput.obj W)) ≫ eS.hom =
      eT.hom ≫ diagramMappingPrecomp (SegalLocalizers.segalMap n) W at hnat
  letI : WeakEquivalence
      (diagramMappingPrecomp (SegalLocalizers.segalMap n) W) :=
    (weakEquivalence_iff _).mpr (hW n hn)
  letI : WeakEquivalence eS.hom := inferInstance
  letI : WeakEquivalence eT.hom := inferInstance
  haveI : WeakEquivalence
      (eT.hom ≫ diagramMappingPrecomp (SegalLocalizers.segalMap n) W) :=
    inferInstance
  exact (weakEquivalence_iff _).mp
    (weakEquivalence_of_postcomp_of_fac hnat)

#print axioms ordinaryInput_segalCondition

end

end DaggerModels.PartII.OrdinaryJTOrdinaryInputSegal
