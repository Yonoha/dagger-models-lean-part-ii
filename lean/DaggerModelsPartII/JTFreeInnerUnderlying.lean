import DaggerModelsPartII.JTFreeInnerFactorization
import ActualInnerAnodyneRigidification

/-!
# Underlying inner-left and vertex preservation of free-inner replacement

Restriction from reversal presheaves to ordinary simplicial sets has a right
Kan extension. Transporting this adjunction across the presheaf equivalence
shows that the underlying map of every free-inner left map is native inner-left.
The native rigidification object theorem then gives vertex bijectivity.
-/

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty Opposite Simplicial DaggerModels
open DaggerModels.OrdinaryRigidification

universe u

namespace DaggerModels.PartII.JTFreeInnerUnderlying

noncomputable section

private instance (A : SSet.{u}) :
    ReverseSimplex.inclusion.op.HasPointwiseRightKanExtension A :=
  fun _ ↦ inferInstance

/-- Right Kan extension gives the actual cofree dagger simplicial set. -/
def cofreeDagger : SSet.{u} ⥤ DaggerSSet.{u} :=
  ReverseSimplex.inclusion.op.ran ⋙ ReversePresheaf.toDaggerSSet

/-- The actual underlying functor is also a left adjoint. -/
def forgetCofreeAdjunction : DaggerSSet.forget.{u} ⊣ cofreeDagger.{u} :=
  (daggerSSetEquivalencePresheaf.toAdjunction.comp
    (ReverseSimplex.inclusion.op.ranAdjunction (Type u))).ofNatIsoLeft
      extensionRestrictionIso

/-- Every actual free-inner left map becomes native inner-left on forgetting dagger. -/
theorem underlying_innerAnodyne {X Y : DaggerSSet.{u}} (i : X ⟶ Y)
    (hi : JTFreeInnerFactorization.innerAnodyne i) :
    DaggerNativeInnerHornFactorization.innerAnodyne i.hom := by
  intro A B p hp
  have hright : JTFreeInnerFactorization.innerFibrations (cofreeDagger.map p) := by
    intro A' B' j hj
    obtain ⟨a⟩ := hj
    exact (forgetCofreeAdjunction.hasLiftingProperty_iff
      (JTFreeInnerReplacement.generator a) p).1
        (JTFreeInnerReplacement.generator_underlying_inner a p hp)
  exact (forgetCofreeAdjunction.hasLiftingProperty_iff i p).2 (hi _ hright)

/-- Degree-zero vertices are bijective for every actual free-inner left map. -/
theorem vertex_bijective {X Y : DaggerSSet.{u}} (i : X ⟶ Y)
    (hi : JTFreeInnerFactorization.innerAnodyne i) :
    Function.Bijective (i.hom.app (op ⦋0⦌)) := by
  have hobj : Function.Bijective (rigidification.map i.hom).obj :=
    DaggerActualInnerAnodyneRigidification.object_bijective i.hom
      (underlying_innerAnodyne i hi)
  constructor
  · intro x x' h
    apply (RigidificationVertices.vertexEquiv X.toSSet).injective
    apply hobj.1
    rw [RigidificationVertices.vertexEquiv_naturality,
      RigidificationVertices.vertexEquiv_naturality]
    exact congrArg (RigidificationVertices.vertexEquiv Y.toSSet) h
  · intro y
    obtain ⟨z, hz⟩ := hobj.2 (RigidificationVertices.vertexEquiv Y.toSSet y)
    obtain ⟨x, rfl⟩ := (RigidificationVertices.vertexEquiv X.toSSet).surjective z
    refine ⟨x, ?_⟩
    apply (RigidificationVertices.vertexEquiv Y.toSSet).injective
    exact (RigidificationVertices.vertexEquiv_naturality i.hom x).symm.trans hz

/-- The whole functorial free-inner unit is native inner-left on forgetting dagger. -/
theorem unit_underlying_innerAnodyne (X : DaggerSSet.{u}) :
    DaggerNativeInnerHornFactorization.innerAnodyne
      (JTFreeInnerFactorization.unit.app X).hom :=
  underlying_innerAnodyne _ (JTFreeInnerFactorization.unit_innerAnodyne X)

/-- The functorial free-inner unit is bijective on actual vertices. -/
theorem unit_vertex_bijective (X : DaggerSSet.{u}) :
    Function.Bijective
      ((JTFreeInnerFactorization.unit.app X).hom.app (op ⦋0⦌)) :=
  vertex_bijective _ (JTFreeInnerFactorization.unit_innerAnodyne X)

end

end DaggerModels.PartII.JTFreeInnerUnderlying
