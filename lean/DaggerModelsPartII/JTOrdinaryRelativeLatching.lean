import DaggerModelsPartII.JTRelativeReedyFrameProperties
import DaggerModelsPartII.OrdinaryBergnerGenerators
import RigidificationCofBase

/-!
# The actual JT relative Reedy arrows after ordinary forgetting

The original opposite comparison has relative latching arrows whose unopposed
outer components are dagger generator-RLP arrows. Forgetting each such arrow
gives the original ordinary trivial-fibration predicate on the same objects
and full Hom maps. This statement precedes comparison with a native relative
latching arrow in the ordinary opposite coefficient category.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite Simplicial
  MorphismProperty DaggerModels
open scoped SSet.modelCategoryQuillen
open DaggerModels.PartII DaggerModels.PartII.JTRelativeReedyFrame

namespace DaggerModels.PartII.JTOrdinaryRelativeLatching

noncomputable section

private local instance : HasLimits Coefficient := daggerSimplicialCatHasLimits
private local instance : HasColimits OppositeOuterDiagram := inferInstance

/-- Forgetting a dagger generator-RLP arrow gives the original ordinary
object-surjective Homwise trivial-fibration class, with no model instance. -/
theorem forget_generators_rlp_ordinaryTrivialFibrations
    {C D : DaggerSimplicialCat.{0, 0}} (p : C ⟶ D)
    (hp : DaggerGeneratingCofibrations.generators.rlp p) :
    DaggerOrdinaryRigidificationCof.ordinaryTrivialFibrations
      (DaggerSimplicialCat.forget.map p) := by
  obtain ⟨ho, hh⟩ := (KanQuillenReuse.generators_rlp_iff_trivial p).mp hp
  refine ⟨ho, ?_⟩
  intro x y
  exact ⟨(hh x y).1,
    (KanQuillenReuse.weakEquivalence_iff_geometric (p.map x y)).mp (hh x y).2⟩

/-- At every original reversal simplex and simplicial degree, the actual
relative latching arrow of the opposite comparison becomes an ordinary
trivial fibration after unopposing and forgetting dagger. -/
theorem forgotten_comparisonOpposite_relativeLatching_ordinaryTrivialFibration
    (m : ReverseSimplex) (n : ℕ) :
    DaggerOrdinaryRigidificationCof.ordinaryTrivialFibrations
      (DaggerSimplicialCat.forget.map
        ((relativeLatchingMap n comparisonOpposite).unop.app m)) := by
  have h := comparisonOpposite_relativeLatching n
  change outerTrivialFibrations (relativeLatchingMap n comparisonOpposite).unop at h
  have hm : DaggerGeneratingCofibrations.generators.rlp
      ((relativeLatchingMap n comparisonOpposite).unop.app m) := h m
  exact forget_generators_rlp_ordinaryTrivialFibrations _ hm

end

end DaggerModels.PartII.JTOrdinaryRelativeLatching
