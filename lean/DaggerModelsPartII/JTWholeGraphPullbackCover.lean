import DaggerModelsPartII.JTPrismChainGraphCover
import DaggerModelsPartII.JTEndpointReducedPullbackCover

/-!
# Pull an old full graph across a new native product, then lift its degree

Reuse search: `JTEndpointReducedPullbackCover.pointwise_pullback` uses
`(IsPullback.of_hasPullback oldπ n).map (evaluation I SSet).obj a` and
`(trivialFibrations SSet).of_isPullback`. Its pointwise lemma is private, so
the same generic pullback theorem is applied here. The second stage uses
`JTPrismChainGraphCover.parameter_projection` and
`JTPrismChainGraphCover.projection_trivialFibration`.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTWholeGraphPullbackCover

noncomputable section

private abbrev J := GroupoidSimplex.parameter

variable {I : Type} [SmallCategory I]
variable {oldY oldX newX : I ⥤ SSet.{0}}
variable (oldπ : oldY ⟶ oldX) (n : newX ⟶ oldX)
variable {K D : I ⥤ SimplexCategory}
variable (oldθ : oldY ⟶ K ⋙ J) (α : D ⟶ K)

/-- The complete old graph fiber over the new native product. -/
abbrev base : I ⥤ SSet.{0} := pullback oldπ n

abbrev baseToOld : base oldπ n ⟶ oldY := pullback.fst oldπ n
abbrev baseToNew : base oldπ n ⟶ newX := pullback.snd oldπ n

/-- The old coefficient parameter on the entire pulled-back graph. -/
abbrev coarseParameter : base oldπ n ⟶ K ⋙ J :=
  baseToOld oldπ n ≫ oldθ

/-- Every compatible lift of the old parameter to the new coefficient degree. -/
abbrev graph : I ⥤ SSet.{0} :=
  JTPrismChainGraphCover.cover (base oldπ n)
    (coarseParameter oldπ n oldθ) α

private abbrev coeffProjection : graph oldπ n oldθ α ⟶ base oldπ n :=
  JTPrismChainGraphCover.projection (base oldπ n)
    (coarseParameter oldπ n oldθ) α

/-- Projection to the new full native product. -/
abbrev projection : graph oldπ n oldθ α ⟶ newX :=
  coeffProjection oldπ n oldθ α ≫ baseToNew oldπ n

/-- Projection to the unchanged old graph, with every old simplex retained. -/
abbrev toOld : graph oldπ n oldθ α ⟶ oldY :=
  coeffProjection oldπ n oldθ α ≫ baseToOld oldπ n

/-- The lifted parameter in the new full coefficient degree. -/
abbrev parameter : graph oldπ n oldθ α ⟶ D ⋙ J :=
  JTPrismChainGraphCover.parameter (base oldπ n)
    (coarseParameter oldπ n oldθ) α

/-- The new parameter recovers exactly the old one after the ordinal map. -/
theorem parameter_old :
    parameter oldπ n oldθ α ≫ Functor.whiskerRight α J =
      toOld oldπ n oldθ α ≫ oldθ := by
  rw [JTPrismChainGraphCover.parameter_projection]
  rfl

/-- Both graph projections describe the same full native product simplex. -/
theorem native_square : toOld oldπ n oldθ α ≫ oldπ =
    projection oldπ n oldθ α ≫ n := by
  simp only [toOld, projection, Category.assoc]
  exact congrArg (coeffProjection oldπ n oldθ α ≫ ·)
    (pullback.condition :
      pullback.fst oldπ n ≫ oldπ = pullback.snd oldπ n ≫ n)

private theorem base_projection_trivial (a : I)
    (hπ : trivialFibrations SSet.{0} (oldπ.app a)) :
    trivialFibrations SSet.{0} ((baseToNew oldπ n).app a) := by
  exact (trivialFibrations SSet.{0}).of_isPullback
    ((IsPullback.of_hasPullback oldπ n).map
      ((CategoryTheory.evaluation I SSet.{0}).obj a)) hπ

/-- The new full graph projection remains a componentwise trivial fibration
after both base change and the surjective ordinal-chain lift. -/
theorem projection_trivialFibration
    (hπ : ∀ a : I, trivialFibrations SSet.{0} (oldπ.app a))
    (hα : ∀ a : I, Function.Surjective (α.app a).toOrderHom)
    (a : I) :
    trivialFibrations SSet.{0} ((projection oldπ n oldθ α).app a) := by
  change trivialFibrations SSet.{0}
    ((coeffProjection oldπ n oldθ α).app a ≫ (baseToNew oldπ n).app a)
  exact (trivialFibrations SSet.{0}).comp_mem _ _
    (JTPrismChainGraphCover.projection_trivialFibration
      (base oldπ n) (coarseParameter oldπ n oldθ) α hα a)
    (base_projection_trivial oldπ n a (hπ a))

end
end DaggerModels.PartII.JTWholeGraphPullbackCover
