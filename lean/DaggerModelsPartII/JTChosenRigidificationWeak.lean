import DaggerModelsPartII.JTChosenOrdinaryAdjoint
import ActualRightConeRigidificationWeak

/-!
# Weakness of the chosen rigidification adjoint

The original dagger rigidification adjoint of the chosen fixed-object
replacement is weak without a cofibrancy premise on the free-inner target.
Its rigidification followed by the original counit is the literal weak
fixed-object replacement map. The proved fibrant-counit theorem and
two-out-of-three give the rigidified weakness, which the original source
weak-class definition reflects. The ordinary Hom consequence retains the
actual underlying adjoint; no ordered mapping-space theorem is asserted.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra DaggerModels
open OrdinaryRigidification
open OrdinaryRigidification.DaggerRigidification
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTChosenRigidificationWeak

open JTChosenOrdinaryAdjoint JTStrictificationCoefficients

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

private local instance : ModelCategory DaggerSSet.{0} :=
  DaggerActualRigidificationQuillen.modelD.{0}
private local instance : ModelCategory DaggerSimplicialCat.{0, 0} :=
  DaggerActualRigidificationQuillen.modelG.{0}

/-- The original counit at the chosen fixed-object coefficient is weak. -/
theorem chosen_counit_weak (W : Source) :
    WeakEquivalence
      (DaggerActualRigidificationQuillen.adjunction.counit.app
        (rigidCoefficient (chosenT W))) :=
  DaggerActualFibrantCounitReduction.fibrant_counit_weak_of_ordinary_local
    DaggerActualRightConeRigidificationWeak.ordinary_counit_local
      (rigidCoefficient (chosenT W)) (rigidCoefficient_fibrant (chosenT W))

/-- The original adjunction triangle is the chosen fixed-object map itself. -/
theorem etaDagger_counit (W : Source) :
    daggerRigidification.map (etaDagger W) ≫
        DaggerActualRigidificationQuillen.adjunction.counit.app
          (rigidCoefficient (chosenT W)) =
      JTObjectPreservingReplacement.r (daggerRigidification.obj (chosenT W)) := by
  calc
    _ = (DaggerActualRigidificationQuillen.adjunction.homEquiv
        (chosenT W) (rigidCoefficient (chosenT W))).symm (etaDagger W) :=
      (DaggerActualRigidificationQuillen.adjunction.homEquiv_counit
        (chosenT W) (rigidCoefficient (chosenT W)) (etaDagger W)).symm
    _ = _ := Equiv.symm_apply_apply _ _

/-- The literal rigidification of the chosen adjoint is original dagger
Bergner weak, using the actual fibrant counit and chosen replacement map. -/
theorem etaRigidified_weak (W : Source) :
    WeakEquivalence (daggerRigidification.map (etaDagger W)) := by
  have hcounit : WeakEquivalence
      (DaggerActualRigidificationQuillen.adjunction.counit.app
        (rigidCoefficient (chosenT W))) := chosen_counit_weak W
  have hcomp : WeakEquivalence
      (daggerRigidification.map (etaDagger W) ≫
        DaggerActualRigidificationQuillen.adjunction.counit.app
          (rigidCoefficient (chosenT W))) := by
    rw [etaDagger_counit]
    exact JTObjectPreservingReplacement.r_weak
      (daggerRigidification.obj (chosenT W))
  exact weakEquivalence_of_postcomp (daggerRigidification.map (etaDagger W))
    (DaggerActualRigidificationQuillen.adjunction.counit.app
      (rigidCoefficient (chosenT W)))

/-- The original dagger Joyal weak class is detected by rigidification,
so the chosen rigidification adjoint is weak without source cofibrancy. -/
theorem etaDagger_weak (W : Source) : WeakEquivalence (etaDagger W) :=
  (DaggerActualQuillenEquivalenceReduction.weakEquivalence_map_iff
    (etaDagger W)).1 (etaRigidified_weak W)

/-- The rigidified map is locally geometrically weak on every original
pair of rigidification objects. -/
theorem etaRigidified_local (W : Source) :
    DaggerGlobalDK.LocalGeometricWeakEquivalence
      (daggerRigidification.map (etaDagger W)) := by
  have h : DaggerGlobalDK.daggerDK DaggerUnitaryInvariance.standardReplacement
      (daggerRigidification.map (etaDagger W)) := by
    rw [← DaggerActualRigidificationQuillen.target_weak]
    exact (weakEquivalence_iff _).mp (etaRigidified_weak W)
  exact h.1

/-- The underlying ordinary rigidification map of the actual chosen
adjoint is a Kan weak map on every original Hom simplicial set. -/
theorem etaOrdinary_hom_weak (W : Source)
    (x y : (rigidification.obj (chosenT W).toSSet).Obj) :
    WeakEquivalence ((rigidification.map (etaOrdinary W)).map x y) := by
  have h := etaRigidified_local W x y
  change DaggerSSetGluing.GW
    ((rigidification.map (etaOrdinary W)).map x y) at h
  exact (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr h

end

end DaggerModels.PartII.JTChosenRigidificationWeak
