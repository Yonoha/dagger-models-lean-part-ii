import DaggerModelsPartII.JTStrictificationCoefficients
import DaggerModelsPartII.JTUnderlyingRightComparison

/-!
# Ordinary adjoints of the chosen dagger strictification map

The chosen free-inner unit and fixed-object replacement determine the literal
ordinary Joyal--Tierney adjoint and the ordinary rigidification adjoint. Their
composite agrees with the ordinary restriction of the actual composite dagger
adjoint, after the specified right-adjoint comparison. This is the strict
compatibility equation used in the ordered-endpoint argument; no weak
equivalence of its ordinary adjoints is asserted here.
-/

set_option autoImplicit false

open CategoryTheory DaggerModels
open OrdinaryRigidification
open OrdinaryRigidification.DaggerRigidification
open OrdinaryRigidification.DaggerNerve

namespace DaggerModels.PartII.JTChosenOrdinaryAdjoint

open JTStrictificationCoefficients JTStrictificationMaps
open DaggerJTAdjunction OrdinaryJTRealization JTReversalInput

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

/-- The specified Bergner target of the chosen free-inner replacement. -/
private abbrev Coefficient (W : Source) := rigidCoefficient (chosenT W)

/-- The dagger rigidification adjoint of the literal fixed-object replacement. -/
def etaDagger (W : Source) :
    chosenT W ⟶ daggerCoherentNerve.obj (Coefficient W) :=
  DaggerActualRigidificationQuillen.adjunction.homEquiv
    (chosenT W) (Coefficient W)
      (JTObjectPreservingReplacement.r (daggerRigidification.obj (chosenT W)))

/-- The original ordinary rigidification adjoint on the same target. -/
def etaOrdinary (W : Source) :
    (chosenT W).toSSet ⟶ coherentNerve.obj (Coefficient W).toSimplicialCat :=
  (etaDagger W).hom

/-- The underlying map is exactly the original ordinary adjoint of the
underlying fixed-object replacement map. -/
theorem etaOrdinary_eq_original_adjoint (W : Source) :
    etaOrdinary W =
      rigidificationCoherentNerveAdjunction.homEquiv
        (chosenT W).toSSet (Coefficient W).toSimplicialCat
          (JTObjectPreservingReplacement.r
            (daggerRigidification.obj (chosenT W))).toEnrichedFunctor := by
  exact (OrdinaryRigidification.daggerRigidificationLiftWitness.homEquiv_compatibility
    (chosenT W) (Coefficient W)
      (JTObjectPreservingReplacement.r (daggerRigidification.obj (chosenT W)))).symm

/-- The ordinary JT transpose of the underlying actual free-inner unit. -/
def gTilde (W : Source) :
    ordinaryInput.obj (Qproj.obj W) ⟶ nerve.obj (chosenT W).toSSet :=
  realizationNerveAdjunction.homEquiv _ _
    (DaggerSSet.forget.map (chosenG W))

/-- The chosen composite dagger adjoint factors through the literal
free-inner unit followed by the dagger rigidification adjoint. -/
theorem chosenAFlat_eq_two_adjoints (W : Source) :
    chosenAFlat W =
      DaggerJTAdjunction.adjunction.homEquiv (Qproj.obj W)
        (daggerCoherentNerve.obj (Coefficient W))
          (chosenG W ≫ etaDagger W) := by
  have hcomp : chosenAFlat W =
      DaggerJTAdjunction.adjunction.homEquiv (Qproj.obj W)
        (daggerCoherentNerve.obj (Coefficient W))
          (DaggerActualRigidificationQuillen.adjunction.homEquiv
            (DaggerJTRealization.daggerRealization.obj (Qproj.obj W))
              (Coefficient W) (chosenA W)) := by
    change (JTCoendMate.compositeAdjunction.homEquiv
      (Qproj.obj W) (Coefficient W) (chosenA W)) = _
    rw [JTCoendMate.compositeAdjunction, Adjunction.comp_homEquiv]
    rfl
  rw [hcomp]
  apply congrArg (DaggerJTAdjunction.adjunction.homEquiv (Qproj.obj W)
    (daggerCoherentNerve.obj (Coefficient W)))
  change DaggerActualRigidificationQuillen.adjunction.homEquiv
      (DaggerJTRealization.daggerRealization.obj (Qproj.obj W)) (Coefficient W)
        (daggerRigidification.map (chosenG W) ≫
          JTObjectPreservingReplacement.r (daggerRigidification.obj (chosenT W))) = _
  exact DaggerActualRigidificationQuillen.adjunction.homEquiv_naturality_left
    (chosenG W)
      (JTObjectPreservingReplacement.r (daggerRigidification.obj (chosenT W)))

/-- Manuscript `jt.eq.underlying-adjoint-compatibility` for the actual
projective, free-inner, and fixed-object choices. -/
theorem chosen_underlying_adjoint_compatibility (W : Source) :
    ordinaryInput.map (chosenAFlat W) ≫
        JTUnderlyingRightComparison.comparison.app
          (daggerCoherentNerve.obj (Coefficient W)) =
      gTilde W ≫ nerve.map (etaOrdinary W) := by
  rw [chosenAFlat_eq_two_adjoints]
  exact JTUnderlyingRightComparison.homEquiv_composite_comparison
    (Qproj.obj W) (chosenG W) (etaDagger W)

end

end DaggerModels.PartII.JTChosenOrdinaryAdjoint
