import DaggerModelsPartII.JTRawFreeInnerComparison
import DaggerModelsPartII.JTGeneralOrderedFiberWeak
import ActualRigHomWeakCoreRigidification

/-!
# The canonical raw comparison on the original ordered fibers

The actual comparison from the chosen projective free-inner target to the
raw free-inner target is weak on every original right-cone mapping space
and on its original strict and chosen ordinary JT endpoint fibers.
This does not prove the raw-unit action or original gTilde action weak.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerModels.OrdinaryRigidification
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTRawFreeInnerOrderedFiber

open JTStrictificationCoefficients JTRawFreeInnerComparison

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

/-- Both endpoints of the actual auxiliary comparison are underlying quasi-categories. -/
private instance chosenTarget_quasicategory (W : Source) :
    (chosenT W).toSSet.Quasicategory := chosenT_quasicategory W

private instance rawTarget_quasicategory (W : Source) :
    (rawTarget W).toSSet.Quasicategory :=
  JTFreeInnerFactorization.replacement_underlying_quasicategory
    (DaggerJTRealization.daggerRealization.obj W)

/-- The canonical comparison acts weakly on the original right-cone mapping spaces. -/
theorem ell_rightMapping_weak (W : Source)
    (x y : (chosenT W).toSSet.obj (op ⦋0⦌)) :
    WeakEquivalence (DaggerActualGeneralRightConeMapping.map (ell W).hom x y) := by
  apply (DaggerActualGeneralIntrinsicLocalComparison.mapping_weak_iff_hom_weak
    (ell W).hom x y).2
  apply (DaggerActualRigHomWeakCoreRigidification.homMap_weak_iff_raw
    (ell W).hom x y).2
  exact ell_rigidified_hom_weak W _ _

/-- The same actual comparison is weak on the literal original strict fibers. -/
theorem ell_strictFiberMap_weak (W : Source)
    (x y : (chosenT W).toSSet.obj (op ⦋0⦌)) :
    WeakEquivalence (JTGeneralOrderedFiberWeak.strictFiberMap (ell W).hom x y) :=
  (DaggerSSetGluing.weakEquivalence_iff_GW _).2
    (JTGeneralOrderedFiberWeak.strictFiberMap_weak_of_rightMapping_weak (ell W).hom x y
      ((DaggerSSetGluing.weakEquivalence_iff_GW _).1 (ell_rightMapping_weak W x y)))

/-- Its original chosen-to-chosen action, with the actual endpoint images, is weak. -/
theorem ell_chosenFiberMap_weak (W : Source)
    (x y : (chosenT W).toSSet.obj (op ⦋0⦌)) :
    WeakEquivalence (JTGeneralOrderedFiberWeak.chosenFiberMap (ell W).hom x y) :=
  (DaggerSSetGluing.weakEquivalence_iff_GW _).2
    (JTGeneralOrderedFiberWeak.chosenFiberMap_weak_of_rightMapping_weak (ell W).hom x y
      ((DaggerSSetGluing.weakEquivalence_iff_GW _).1 (ell_rightMapping_weak W x y)))

end

end DaggerModels.PartII.JTRawFreeInnerOrderedFiber
