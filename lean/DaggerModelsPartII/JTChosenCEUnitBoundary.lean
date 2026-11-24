import DaggerModelsPartII.JTChosenOrdinaryAdjoint
import DaggerModelsPartII.JTEndpointObjects
import DaggerModelsPartII.JTCEPlainMappingTarget
import DaggerModelsPartII.UnderReedyCriterion
import NativeJoyalWeakTrivialFibrationSpan
import OriginalOrdinaryNerveQuasicategory

/-!
# The chosen ordinary unit under its literal ordered boundary

The source and target boundary maps record the two vertices in order. The
ordinary adjoint of the actual fixed-object replacement gives a morphism
under that same boundary. Both targets are fibrant in the original ordinary
Joyal undercategory. Weakness of the ordinary unit is not asserted.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.JTChosenCEUnitBoundary

open JTEndpointObjects JTStrictificationCoefficients JTChosenOrdinaryAdjoint

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

private def ordinaryJoyalModel : ModelCategory SSet.{0} :=
  DaggerActualDCHRightInducedAndMainTheoremD.ordinaryJoyalModel.{0}

private local instance : ModelCategory SSet.{0} := ordinaryJoyalModel
private local instance : CategoryWithWeakEquivalences SSet.{0} :=
  ordinaryJoyalModel.categoryWithWeakEquivalences
private local instance : CategoryWithFibrations SSet.{0} :=
  ordinaryJoyalModel.categoryWithFibrations
private local instance : CategoryWithCofibrations SSet.{0} :=
  ordinaryJoyalModel.categoryWithCofibrations

private local instance : ModelCategory (Under boundary) :=
  JTEndpointCobase.underModel boundary
private local instance : CategoryWithFibrations (Under boundary) :=
  (JTEndpointCobase.underModel boundary).categoryWithFibrations

/-- The ordinary coherent nerve of the actual fixed-object Bergner target. -/
abbrev chosenNerve (W : Source) : SSet.{0} :=
  DaggerModels.OrdinaryRigidification.coherentNerve.obj
    (rigidCoefficient (chosenT W)).toSimplicialCat

/-- The two literal images of the ordered source vertices. -/
def chosenVertices (W : Source)
    (x y : (chosenT W).toSSet.obj (op ⦋0⦌)) :
    (chosenNerve W).obj (op ⦋0⦌) × (chosenNerve W).obj (op ⦋0⦌) :=
  ((etaOrdinary W).app (op ⦋0⦌) x,
    (etaOrdinary W).app (op ⦋0⦌) y)

/-- The original ordered source boundary. -/
def sourceBoundary (W : Source)
    (x y : (chosenT W).toSSet.obj (op ⦋0⦌)) :
    boundary ⟶ (chosenT W).toSSet :=
  (boundaryHomEquiv (chosenT W).toSSet).symm (x, y)

/-- The boundary of the chosen ordinary coherent-nerve target. -/
def targetBoundary (W : Source)
    (x y : (chosenT W).toSSet.obj (op ⦋0⦌)) :
    boundary ⟶ chosenNerve W :=
  (boundaryHomEquiv (chosenNerve W)).symm (chosenVertices W x y)

def sourceUnder (W : Source)
    (x y : (chosenT W).toSSet.obj (op ⦋0⦌)) : Under boundary :=
  Under.mk (sourceBoundary W x y)

def targetUnder (W : Source)
    (x y : (chosenT W).toSSet.obj (op ⦋0⦌)) : Under boundary :=
  Under.mk (targetBoundary W x y)

/-- Naturality of the literal boundary classifier for this chosen unit. -/
theorem eta_boundary (W : Source)
    (x y : (chosenT W).toSSet.obj (op ⦋0⦌)) :
    sourceBoundary W x y ≫ etaOrdinary W = targetBoundary W x y := by
  apply (boundaryHomEquiv (chosenNerve W)).injective
  rw [show (boundaryHomEquiv (chosenNerve W)) (targetBoundary W x y) =
      chosenVertices W x y from
    (boundaryHomEquiv (chosenNerve W)).apply_symm_apply (chosenVertices W x y)]
  apply Prod.ext
  · change SSet.yonedaEquiv
        (SSet.boundary₁.ι₀ ≫ (sourceBoundary W x y ≫ etaOrdinary W)) =
        (etaOrdinary W).app (op ⦋0⦌) x
    rw [← Category.assoc, SSet.yonedaEquiv_comp]
    have h := (boundaryHomEquiv (chosenT W).toSSet).apply_symm_apply (x, y)
    exact congrArg ((etaOrdinary W).app (op ⦋0⦌)) (congrArg Prod.fst h)
  · change SSet.yonedaEquiv
        (SSet.boundary₁.ι₁ ≫ (sourceBoundary W x y ≫ etaOrdinary W)) =
        (etaOrdinary W).app (op ⦋0⦌) y
    rw [← Category.assoc, SSet.yonedaEquiv_comp]
    have h := (boundaryHomEquiv (chosenT W).toSSet).apply_symm_apply (x, y)
    exact congrArg ((etaOrdinary W).app (op ⦋0⦌)) (congrArg Prod.snd h)

/-- The exact chosen ordinary adjoint as a map under both ordered endpoints. -/
def etaUnder (W : Source)
    (x y : (chosenT W).toSSet.obj (op ⦋0⦌)) :
    sourceUnder W x y ⟶ targetUnder W x y :=
  Under.homMk (etaOrdinary W) (eta_boundary W x y)

@[simp] theorem etaUnder_right (W : Source)
    (x y : (chosenT W).toSSet.obj (op ⦋0⦌)) :
    (etaUnder W x y).right = etaOrdinary W := rfl

/-- The original Joyal fibrations are the native candidate fibrations. -/
private theorem fibrant_of_quasicategory (X : SSet.{0}) [X.Quasicategory] :
    IsFibrant X := by
  apply (isFibrant_iff_of_isTerminal (terminal.from X)
    (terminalIsTerminal : IsTerminal (⊤_ SSet.{0}))).mpr
  rw [fibration_iff]
  change ordinaryJoyalModel.categoryWithFibrations.fibrations (terminal.from X)
  rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelFib,
    DaggerNativeFullWeakSmithGenerators.boundary_cof]
  exact DaggerNativeJoyalWeakTrivialFibrationSpan.terminal_candidate X

/-- The chosen free-inner target is fibrant under its literal boundary in
the original ordinary Joyal model. -/
theorem sourceUnder_fibrant (W : Source)
    (x y : (chosenT W).toSSet.obj (op ⦋0⦌)) :
    IsFibrant (sourceUnder W x y) := by
  apply (UnderReedyCriterion.under_isFibrant_iff boundary _).2
  change IsFibrant (chosenT W).toSSet
  letI : (chosenT W).toSSet.Quasicategory := chosenT_quasicategory W
  exact fibrant_of_quasicategory _

/-- The nerve of the chosen fixed-object Bergner-fibrant coefficient is
fibrant under its literal image boundary in the original ordinary model. -/
theorem targetUnder_fibrant (W : Source)
    (x y : (chosenT W).toSSet.obj (op ⦋0⦌)) :
    IsFibrant (targetUnder W x y) := by
  apply (UnderReedyCriterion.under_isFibrant_iff boundary _).2
  change IsFibrant (chosenNerve W)
  have hKan :=
    (DaggerActualFibrantCounitReduction.fibrant_iff_localKan
      (rigidCoefficient (chosenT W))).1
        (rigidCoefficient_fibrant (chosenT W))
  letI : (chosenNerve W).Quasicategory :=
    DaggerOrdinaryRigidificationCof.OriginalNerveQuasicategory.coherentNerve_quasicategory
      (rigidCoefficient (chosenT W)).toSimplicialCat hKan
  exact fibrant_of_quasicategory _

/-- Conditional target invariance for the exact chosen ordinary unit. The
original ordinary Joyal weakness of this unit remains an explicit input. -/
theorem plainCEHomMap_eta_weak_of_ordinary_weak (W : Source)
    (x y : (chosenT W).toSSet.obj (op ⦋0⦌))
    (hη : DaggerNativeJoyalMappingTest.weakCategoricalEquivalences
      (etaOrdinary W)) :
    DaggerSSetGluing.GW
      (JTCEPlainMappingTarget.plainCEHomMap (etaUnder W x y)) := by
  exact @JTCEPlainMappingTarget.plainCEHomMap_weak
    (sourceUnder W x y) (targetUnder W x y)
    (sourceUnder_fibrant W x y) (targetUnder_fibrant W x y)
    (etaUnder W x y) hη

end

end DaggerModels.PartII.JTChosenCEUnitBoundary
