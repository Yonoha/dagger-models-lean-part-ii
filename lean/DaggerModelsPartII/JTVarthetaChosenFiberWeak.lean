import DaggerModelsPartII.JTAFlatOrderedFiberAction
import DaggerModelsPartII.JTXiChosenFiber
import DaggerModelsPartII.JTChosenRightMappingUnit
import DaggerModelsPartII.JTOrdinaryEndpointFibration

/-!
# The actual right-comparison action on chosen ordered fibers

For the original dagger right-adjoint endpoint arrow at the chosen fibrant
coefficient, the strict fiber comparison is the checked original comparison
isomorphism. The literal dagger and ordinary endpoint arrows are Kan
fibrations. Consequently its actual selected chosen-fiber action is Kan weak.
This does not assert weakness of the chosen `gTilde` or `aFlat` actions.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTVarthetaChosenFiberWeak

open JTRightAdjointOrderedFiber JTStrictificationCoefficients
open JTAFlatOrderedFiberAction

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev X (W : Source) :=
  OrdinaryRigidification.DaggerNerve.daggerCoherentNerve.obj
    (rigidCoefficient (chosenT W))

/-- The exact strict-fiber map underlying the chosen right-comparison
square. Its total and base maps are the original `comparisonRow` maps. -/
def strictComparisonMap (W : Source)
    (u v : (X W).toSSet.obj (op ⦋0⦌))
    (hb : daggerEndpointPoint (X W) u v ≫
        JTAFlatOrderedFiberAction.comparisonBase W =
          ordinaryEndpointPoint (X W) u v) :
    daggerOrderedFiber (X W) u v ⟶ ordinaryOrderedFiber (X W) u v :=
  DaggerNativeSSetFibrationSquareFibreWeak.fibreMap
    (daggerEndpointArrow (X W))
    (ordinaryEndpointArrow (X W).toSSet)
    (comparisonRow (X W) ⦋1⦌)
    (JTAFlatOrderedFiberAction.comparisonBase W)
    (JTRightEndpointCartesian.endpoint_square (X W))
    (daggerEndpointPoint (X W) u v)
    (ordinaryEndpointPoint (X W) u v)
    hb

/-- The strict map is literally the original right-comparison fiber map,
proved through both pullback projections rather than an objectwise iso. -/
theorem strictComparisonMap_eq (W : Source)
    (u v : (X W).toSSet.obj (op ⦋0⦌))
    (hb : daggerEndpointPoint (X W) u v ≫
        JTAFlatOrderedFiberAction.comparisonBase W =
          ordinaryEndpointPoint (X W) u v) :
    strictComparisonMap W u v hb = comparisonFiber (X W) u v := by
  apply pullback.hom_ext
  · simp only [strictComparisonMap,
      DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_fst,
      comparisonFiber_fst]
  · simp only [strictComparisonMap,
      DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_snd,
      comparisonFiber_snd]

/-- The canonical strict-to-chosen inclusions identify this chosen map
with the original strict comparison before localization. -/
theorem comparisonChosenMap_inclusion (W : Source)
    (u v : (X W).toSSet.obj (op ⦋0⦌)) :
    ChosenHomotopyFiberTriangle.inclusion
        (daggerEndpointArrow (X W)) (daggerEndpointPoint (X W) u v) ≫
      comparisonChosenMap W u v =
      comparisonFiber (X W) u v ≫
        ChosenHomotopyFiberTriangle.inclusion
          (ordinaryEndpointArrow (X W).toSSet)
          (ordinaryEndpointPoint (X W) u v) := by
  unfold comparisonChosenMap
  rw [ChosenHomotopyFiberFunctor.inclusion_chosenMap]
  rw [show DaggerNativeSSetFibrationSquareFibreWeak.fibreMap
      (daggerEndpointArrow (X W))
      (ordinaryEndpointArrow (X W).toSSet)
      (comparisonRow (X W) ⦋1⦌)
      (JTAFlatOrderedFiberAction.comparisonBase W)
      (JTRightEndpointCartesian.endpoint_square (X W))
      (daggerEndpointPoint (X W) u v)
      (ordinaryEndpointPoint (X W) u v) _ =
      comparisonFiber (X W) u v from strictComparisonMap_eq W u v _]

/-- The selected comparison map on actual chosen fibers is Kan weak at
both original ordered vertices, with no source-fiber fibrancy hypothesis. -/
theorem comparisonChosenMap_weak (W : Source)
    (u v : (X W).toSSet.obj (op ⦋0⦌)) :
    WeakEquivalence (comparisonChosenMap W u v) := by
  letI : (X W).toSSet.Quasicategory := by
    change (JTChosenCEUnitBoundary.chosenNerve W).Quasicategory
    exact JTChosenRightMappingUnit.chosenNerve_quasicategory W
  haveI : Fibration (daggerEndpointArrow (X W)) :=
    JTXiChosenFiber.daggerEndpointArrow_fibration (X W)
  haveI : Fibration (ordinaryEndpointArrow (X W).toSSet) :=
    JTOrdinaryEndpointFibration.ordinaryEndpointArrow_fibration (X W).toSSet
  haveI : IsIso (comparisonFiber (X W) u v) :=
    comparisonFiber_isIso (X W) u v
  haveI : WeakEquivalence (comparisonFiber (X W) u v) :=
    (weakEquivalence_iff _).mpr ((weakEquivalences SSet.{0}).of_isIso _)
  haveI : WeakEquivalence
      (ChosenHomotopyFiberTriangle.inclusion
        (daggerEndpointArrow (X W)) (daggerEndpointPoint (X W) u v)) :=
    ChosenHomotopyFiberTriangle.inclusion_weak _ _
  haveI : WeakEquivalence
      (ChosenHomotopyFiberTriangle.inclusion
        (ordinaryEndpointArrow (X W).toSSet)
        (ordinaryEndpointPoint (X W) u v)) :=
    ChosenHomotopyFiberTriangle.inclusion_weak _ _
  haveI : WeakEquivalence
      (comparisonFiber (X W) u v ≫
        ChosenHomotopyFiberTriangle.inclusion
          (ordinaryEndpointArrow (X W).toSSet)
          (ordinaryEndpointPoint (X W) u v)) := inferInstance
  exact weakEquivalence_of_precomp_of_fac
    (comparisonChosenMap_inclusion W u v)

end

end DaggerModels.PartII.JTVarthetaChosenFiberWeak
