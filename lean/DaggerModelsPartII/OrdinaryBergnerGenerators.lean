import OriginalOrdinaryCellFinitePresentability
import OriginalOrdinaryCellLifting
import RigidificationCofBase
import DaggerModels.SmallObjectFiniteDomains
import DaggerModels.SimplicialColimits
import DaggerModels.SimplicialObjectAdjunctions
import DaggerModels.DaggerDiscreteObjects
import DaggerModels.DaggerSimplicialCofree
import Mathlib.CategoryTheory.SmallObject.Basic

/-!
# Ordinary Bergner boundary and object generators

The actual ordinary two-object boundary cells and the discrete object cell
detect the existing surjective local trivial fibrations. The small object
argument expresses their left lifting class as retracts of relative cells.
This does not introduce an ordinary model-category structure.
-/

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.OrdinaryBergnerGenerators

noncomputable section

/-- The actual ordinary image of the Part I empty dagger category. -/
abbrev empty : SimplicialCat.{u, u} :=
  DaggerSimplicialCat.forget.obj DaggerDiscreteObjects.empty

/-- The actual ordinary image of the Part I dagger point. -/
abbrev point : SimplicialCat.{u, u} :=
  DaggerSimplicialCat.forget.obj DaggerDiscreteObjects.point

/-- The original discrete-object functor's map from no objects to one object. -/
def emptyToPoint : empty.{u} ⟶ point.{u} :=
  DaggerSimplicialCat.forget.map DaggerDiscreteObjects.emptyToPoint

private def emptyIsInitial : IsInitial empty.{u} :=
  letI : PreservesColimitsOfSize.{0, 0} DaggerSimplicialCat.forget.{u, u} :=
    DaggerSimplicialCat.Cofree.forget_preservesColimitsOfSize
  DaggerDiscreteObjects.emptyIsInitial.isInitialObj
    DaggerSimplicialCat.forget DaggerDiscreteObjects.empty

/-- Lifting against the ordinary object generator detects exact object
surjectivity, including when the source category is empty. -/
theorem object_hasLiftingProperty_iff_surjective
    {C D : SimplicialCat.{u, u}} (p : C ⟶ D) :
    HasLiftingProperty emptyToPoint.{u} p ↔ Function.Surjective p.obj := by
  have hAdj := DaggerSimplicialCat.Cofree.adjunction.hasLiftingProperty_iff
    DaggerDiscreteObjects.emptyToPoint p
  constructor
  · intro h
    exact (DaggerDiscreteObjects.hasLiftingProperty_iff_surjective
      (DaggerSimplicialCat.Cofree.functor.map p)).1 (hAdj.mp h)
  · intro h
    exact hAdj.mpr ((DaggerDiscreteObjects.hasLiftingProperty_iff_surjective
      (DaggerSimplicialCat.Cofree.functor.map p)).2 h)

/-- Every dimension, including zero, supplies an actual ordinary free edge
boundary cell. -/
def boundaryGenerators : MorphismProperty SimplicialCat.{u, u} :=
  .ofHoms (fun n : ℕ ↦ OrdinaryTwoObjectCell.functor.map (SSet.boundary.{u} n).ι)

/-- The literal ordinary object generator as a singleton family. -/
def objectGenerators : MorphismProperty SimplicialCat.{u, u} :=
  .ofHoms (fun _ : Unit ↦ emptyToPoint.{u})

/-- The ordinary boundary-cell and object-cell generating family. -/
def generators : MorphismProperty SimplicialCat.{u, u} :=
  boundaryGenerators ⊔ objectGenerators

variable {C D : SimplicialCat.{u, u}} (p : C ⟶ D)

theorem boundary_rlp_iff : boundaryGenerators.rlp p ↔
    ∀ (x y : C.Obj) (n : ℕ),
      HasLiftingProperty (SSet.boundary.{u} n).ι (p.map x y) := by
  constructor
  · intro hp x y n
    exact (OriginalOrdinaryCellLifting.hasLiftingProperty_iff _ p).1
      (hp _ (.mk n)) x y
  · intro hp A B f hf
    cases hf with
    | mk n =>
      exact (OriginalOrdinaryCellLifting.hasLiftingProperty_iff _ p).2
        (fun x y ↦ hp x y n)

theorem object_rlp_iff : objectGenerators.rlp p ↔ Function.Surjective p.obj := by
  constructor
  · intro hp
    exact (object_hasLiftingProperty_iff_surjective p).1
      (hp _ (.mk Unit.unit))
  · intro hp A B f hf
    cases hf with
    | mk _ => exact (object_hasLiftingProperty_iff_surjective p).2 hp

theorem generators_rlp_iff : generators.rlp p ↔
    Function.Surjective p.obj ∧
      ∀ (x y : C.Obj) (n : ℕ),
        HasLiftingProperty (SSet.boundary.{u} n).ι (p.map x y) := by
  constructor
  · intro hp
    have ho : objectGenerators.rlp p := by
      intro A B f hf
      exact hp f (Or.inr hf)
    have hb : boundaryGenerators.rlp p := by
      intro A B f hf
      exact hp f (Or.inl hf)
    exact ⟨(object_rlp_iff p).1 ho, (boundary_rlp_iff p).1 hb⟩
  · rintro ⟨ho, hb⟩ A B f hf
    change boundaryGenerators f ∨ objectGenerators f at hf
    rcases hf with hf | hf
    · exact (boundary_rlp_iff p).2 hb f hf
    · exact (object_rlp_iff p).2 ho f hf

/-- The generator RLP is the original ordinary surjective local Kan trivial
fibration class, with the original geometric weak-equivalence predicate. -/
theorem generators_rlp_iff_ordinaryTrivialFibrations :
    generators.rlp p ↔
      DaggerOrdinaryRigidificationCof.ordinaryTrivialFibrations p := by
  rw [generators_rlp_iff]
  change (Function.Surjective p.obj ∧
      ∀ (x y : C.Obj) (n : ℕ),
        HasLiftingProperty (SSet.boundary.{u} n).ι (p.map x y)) ↔
      (Function.Surjective p.obj ∧
        ∀ x y, Fibration (p.map x y) ∧
          DaggerOrdinaryRigidificationCof.geometric (p.map x y))
  constructor
  · rintro ⟨ho, hh⟩
    refine ⟨ho, ?_⟩
    intro x y
    exact (DaggerOrdinaryRigidificationCof.scalar_iff_rlp (p.map x y)).mpr
      ((KanQuillenReuse.boundary_lifting_iff_rlp (p.map x y)).mp (hh x y))
  · rintro ⟨ho, hh⟩
    refine ⟨ho, ?_⟩
    intro x y
    exact (KanQuillenReuse.boundary_lifting_iff_rlp (p.map x y)).mpr
      ((DaggerOrdinaryRigidificationCof.scalar_iff_rlp (p.map x y)).mp (hh x y))

theorem generators_rlp_eq_ordinaryTrivialFibrations :
    generators.rlp =
      DaggerOrdinaryRigidificationCof.ordinaryTrivialFibrations.{u} := by
  ext C D p
  exact generators_rlp_iff_ordinaryTrivialFibrations p

/-- The ordinary generating family is small at its original universe. -/
theorem generators_isSmall : MorphismProperty.IsSmall.{u} generators.{u} := by
  have hb : MorphismProperty.IsSmall.{u} boundaryGenerators.{u} := by
    dsimp [boundaryGenerators]
    infer_instance
  have ho : MorphismProperty.IsSmall.{u} objectGenerators.{u} := by
    dsimp [objectGenerators]
    infer_instance
  letI := hb
  letI := ho
  exact SmallObjectFiniteDomains.isSmall_sup boundaryGenerators objectGenerators

/-- Every literal ordinary generator domain is finitely presentable. -/
theorem generators_domain_isFinitelyPresentable
    {A B : SimplicialCat.{u, u}} (i : A ⟶ B)
    (hi : generators i) : IsFinitelyPresentable.{u} A := by
  change boundaryGenerators i ∨ objectGenerators i at hi
  rcases hi with hi | hi
  · cases hi with
    | mk n =>
      exact OrdinaryTwoObjectCell.cell_finite_isFinitelyPresentable
        (SSet.boundary n : SSet)
  · cases hi with
    | mk _ =>
      exact SmallObjectFiniteDomains.initial_isFinitelyPresentable
        emptyIsInitial

/-- This literal ordinary family satisfies Mathlib's small object argument. -/
theorem generators_hasSmallObjectArgument :
    MorphismProperty.HasSmallObjectArgument.{u} generators.{u} := by
  have : HasColimitsOfSize.{u, u} SimplicialCat.{u, u} :=
    SimplicialCat.SemanticColimit.simplicialCatHasColimits
  have := generators_isSmall.{u}
  exact SmallObjectFiniteDomains.hasSmallObjectArgument.{u} generators
    generators_domain_isFinitelyPresentable

/-- Original ordinary cofibrations are retracts of transfinite composites of
pushouts of coproducts of the same literal boundary and object cells. -/
theorem ordinaryCofibrations_eq_retract_cells :
    DaggerOrdinaryRigidificationCof.ordinaryCofibrations.{u} =
      (MorphismProperty.transfiniteCompositions.{u}
        (MorphismProperty.coproducts.{u} generators.{u}).pushouts).retracts := by
  letI := generators_hasSmallObjectArgument.{u}
  rw [DaggerOrdinaryRigidificationCof.ordinaryCofibrations,
    ← generators_rlp_eq_ordinaryTrivialFibrations]
  exact MorphismProperty.llp_rlp_of_hasSmallObjectArgument
    (I := generators.{u})

end

end DaggerModels.OrdinaryBergnerGenerators
