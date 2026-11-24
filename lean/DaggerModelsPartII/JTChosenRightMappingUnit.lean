import DaggerModelsPartII.JTChosenCEUnitBoundary
import DaggerModelsPartII.JTChosenRigidificationWeak
import ActualRigHomWeakCoreRigidification

/-!
# The actual chosen unit on original right-cone mapping spaces

The underlying ordinary adjoint of the fixed-object replacement induces a
Kan weak map on each original right-cone mapping simplicial set. This uses
the original rigidification Hom criterion and retains the literal images of
both ordered vertices. It makes no claim that the ordinary unit is a Joyal
weak equivalence or that the CE mapping map is weak.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra Opposite Simplicial DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTChosenRightMappingUnit

open JTChosenOrdinaryAdjoint JTStrictificationCoefficients
open JTChosenCEUnitBoundary JTChosenRigidificationWeak

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

/-- The original ordinary coherent nerve of the chosen Bergner-fibrant
fixed-object coefficient is an actual quasi-category. -/
theorem chosenNerve_quasicategory (W : Source) :
    (chosenNerve W).Quasicategory := by
  have hKan :=
    (DaggerActualFibrantCounitReduction.fibrant_iff_localKan
      (rigidCoefficient (chosenT W))).1
        (rigidCoefficient_fibrant (chosenT W))
  exact DaggerOrdinaryRigidificationCof.OriginalNerveQuasicategory.coherentNerve_quasicategory
      (rigidCoefficient (chosenT W)).toSimplicialCat hKan

/-- The literal map of original right-cone mapping simplicial sets at the
chosen ordered source vertices is Kan weak, without an ordinary Joyal
weakness premise on the chosen unit. -/
theorem etaOrdinary_rightMapping_weak (W : Source)
    (x y : (chosenT W).toSSet.obj (op ⦋0⦌)) :
    WeakEquivalence
      (DaggerActualGeneralRightConeMapping.map (etaOrdinary W) x y) := by
  letI : (chosenT W).toSSet.Quasicategory := chosenT_quasicategory W
  letI : (chosenNerve W).Quasicategory := chosenNerve_quasicategory W
  apply (DaggerActualGeneralIntrinsicLocalComparison.mapping_weak_iff_hom_weak
    (etaOrdinary W) x y).2
  apply (DaggerActualRigHomWeakCoreRigidification.homMap_weak_iff_raw
    (etaOrdinary W) x y).2
  exact etaOrdinary_hom_weak W
    (DaggerModels.OrdinaryRigidification.RigidificationVertices.vertexEquiv
      (chosenT W).toSSet x)
    (DaggerModels.OrdinaryRigidification.RigidificationVertices.vertexEquiv
      (chosenT W).toSSet y)

/-- The same actual map in the repository's scalar geometric weak class. -/
theorem etaOrdinary_rightMapping_GW (W : Source)
    (x y : (chosenT W).toSSet.obj (op ⦋0⦌)) :
    DaggerSSetGluing.GW
      (DaggerActualGeneralRightConeMapping.map (etaOrdinary W) x y) :=
  (DaggerSSetGluing.weakEquivalence_iff_GW _).mp
    (etaOrdinary_rightMapping_weak W x y)

end

end DaggerModels.PartII.JTChosenRightMappingUnit
