import DaggerModelsPartII.JTTransportUnitTriangle
import DaggerModelsPartII.DerivedUnitQuillenCriterion
import DaggerModelsPartII.TheoremCStatement
import ProofActualDaggerQuillenEquivalence

/-!
# The literal chosen delta-unit transport triangle

The replacement is exactly DerivedUnitQuillenCriterion.replacementData for
original delta and the injective Segal model. The actual delta derived unit
followed by the vertex of a frame adjoint is identified with the original
rigidification adjoint under the specified Theta and Omega. This equation
asserts no weakness of the derived unit or of the frame realization of the
replacement map.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra DaggerModels
open OrdinaryRigidification.DaggerRigidification

namespace DaggerModels.PartII.JTChosenUnitTriangle

open ConstantVertexAdjunction JTFrameAdjunction JTStrictTransport
open JTTransportUnitTriangle SegalLocalizers

noncomputable section

private local instance : HasLimits DaggerSSet.{0} := daggerSSetHasLimits
private local instance : HasColimits DaggerSSet.{0} := daggerSSetHasColimits
private local instance : ModelCategory DaggerSSet.{0} :=
  DaggerOriginalJoyalModel.standardModelCategory.{0}
private local instance : ModelCategory ReverseDaggerSpace.{0} := injectiveSegalModel
private local instance : ModelCategory DaggerSimplicialCat.{0, 0} :=
  DaggerActualRigidificationQuillen.modelG.{0}

/-- The replacement is the one fixed in the actual final Quillen criterion. -/
def chosenReplacement (X : DaggerSSet.{0}) :=
  DerivedUnitQuillenCriterion.replacementData delta X

/-- The actual fixed delta derived unit, for the original two model structures. -/
def chosenDerivedUnit (X : DaggerSSet.{0}) :
    X ⟶ vertex.obj (chosenReplacement X).Z :=
  DerivedUnitQuillenCriterion.derivedUnit delta vertex ConstantVertexAdjunction.adjunction X

/-- Transport a map out of the realized chosen replacement to the original
rigidification source via the specified inverse Theta. -/
def rigidificationComparison (X : DaggerSSet.{0}) (C : DaggerSimplicialCat.{0, 0})
    (b : frameRealization.obj (chosenReplacement X).Z ⟶ C) :
    daggerRigidification.obj X ⟶ C :=
  Theta.inv.app X ≫ frameRealization.map (chosenReplacement X).i ≫ b

/-- The transported strict frame adjoint uses exactly the chosen replacement
map, followed by the actual frame adjoint of b. -/
theorem transportedFrameAdjoint_comparison (X : DaggerSSet.{0})
    (C : DaggerSimplicialCat.{0, 0})
    (b : frameRealization.obj (chosenReplacement X).Z ⟶ C) :
    transportedFrameAdjoint X C (rigidificationComparison X C b) =
      (chosenReplacement X).i ≫
        JTFrameAdjunction.adjunction.homEquiv (chosenReplacement X).Z C b := by
  unfold transportedFrameAdjoint rigidificationComparison
  rw [← Category.assoc, Iso.hom_inv_id_app]
  simpa only [Functor.comp_obj, Category.id_comp] using
    JTFrameAdjunction.adjunction.homEquiv_naturality_left (chosenReplacement X).i b

/-- The actual chosen delta-unit triangle. The unit is the literal map from
the final criterion, with original target injectiveSegalModel and no
replacement by another adjunction's derived unit. -/
theorem chosen_unit_triangle (X : DaggerSSet.{0})
    (C : DaggerSimplicialCat.{0, 0})
    (b : frameRealization.obj (chosenReplacement X).Z ⟶ C) :
    (chosenDerivedUnit X ≫
      vertex.map (JTFrameAdjunction.adjunction.homEquiv (chosenReplacement X).Z C b)) ≫
        Omega.hom.app C =
      DaggerActualRigidificationQuillen.adjunction.homEquiv X C
        (rigidificationComparison X C b) := by
  have h := unit_triangle X C (rigidificationComparison X C b)
  rw [transportedFrameAdjoint_comparison, Functor.map_comp] at h
  simpa only [chosenDerivedUnit, DerivedUnitQuillenCriterion.derivedUnit,
    chosenReplacement, Category.assoc] using h


/-- Part I identifies the actual chosen-unit composite weak test with the
original dagger DK weak test on its specified rigidification comparison.
This does not supply a weak frame adjoint or assert that the unit is weak. -/
theorem chosen_unit_composite_weak_iff (X : DaggerSSet.{0}) [IsCofibrant X]
    (C : DaggerSimplicialCat.{0, 0}) [IsFibrant C]
    (b : frameRealization.obj (chosenReplacement X).Z ⟶ C) :
    WeakEquivalence (chosenDerivedUnit X ≫
      vertex.map (JTFrameAdjunction.adjunction.homEquiv (chosenReplacement X).Z C b)) ↔
        WeakEquivalence (rigidificationComparison X C b) := by
  letI : DaggerActualRigidificationQuillen.adjunction.{0}.IsQuillenEquivalence :=
    DaggerActualDaggerQuillenEquivalenceProof.quillen_verified.{0}
  calc
    _ ↔ WeakEquivalence ((chosenDerivedUnit X ≫
        vertex.map (JTFrameAdjunction.adjunction.homEquiv (chosenReplacement X).Z C b)) ≫
          Omega.hom.app C) := (weakEquivalence_postcomp_iff _ _).symm
    _ ↔ WeakEquivalence (DaggerActualRigidificationQuillen.adjunction.homEquiv X C
          (rigidificationComparison X C b)) := by rw [chosen_unit_triangle]
    _ ↔ _ := DaggerActualRigidificationQuillen.adjunction.weakEquivalence_homEquiv_iff _

end

end DaggerModels.PartII.JTChosenUnitTriangle
