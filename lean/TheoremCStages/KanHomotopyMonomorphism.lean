import OrdinarySegalCoherentEvaluationTrivialFibration
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono

/-!
# Strict diagonals of maps onto a union of components

The existing `PullbackCone.isLimitOfFactors` cancels a common monomorphism
from a pullback. Thus a Kan trivial fibration followed by a monomorphism
has weak strict diagonal. This applies to the original coherent evaluation,
with its actual coherent-arrow inclusion, without a completeness hypothesis.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.KanHomotopyMonomorphism

noncomputable section

/-- The literal diagonal into the strict self-pullback of the same map. -/
def diagonal {X Y : SSet.{0}} (f : X ⟶ Y) : X ⟶ pullback f f :=
  pullback.lift (𝟙 X) (𝟙 X) (by rw [Category.id_comp])

/-- A common monomorphic factor can be cancelled from the actual pullback. -/
theorem selfPullback_of_mono_factor {X I Y : SSet.{0}}
    (f : X ⟶ Y) (p : X ⟶ I) (m : I ⟶ Y) [Mono m] (fac : p ≫ m = f) :
    IsPullback (pullback.fst f f) (pullback.snd f f) p p := by
  exact IsPullback.of_isLimit
    (PullbackCone.isLimitOfFactors f f m p p fac fac
      (PullbackCone.mk (pullback.fst f f) (pullback.snd f f)
        (pullback.condition (f := f) (g := f)))
      (IsPullback.of_hasPullback f f).isLimit)

/-- A Kan trivial fibration followed by a mono has weak strict diagonal.
The original map and both actual projections are retained. -/
theorem diagonal_weak_of_trivialFibration_mono {X I Y : SSet.{0}}
    (f : X ⟶ Y) (p : X ⟶ I) (m : I ⟶ Y) [Mono m] (fac : p ≫ m = f)
    (hp : trivialFibrations SSet.{0} p) : WeakEquivalence (diagonal f) := by
  have hs := selfPullback_of_mono_factor f p m fac
  have ht := (trivialFibrations SSet.{0}).of_isPullback hs hp
  have : WeakEquivalence (pullback.snd f f) :=
    ((mem_trivialFibrations_iff _).mp ht).2
  have h : diagonal f ≫ pullback.snd f f = 𝟙 X := pullback.lift_snd _ _ _
  exact weakEquivalence_of_postcomp_of_fac h

private local instance : ModelCategory OrdinaryCSSLocalization.Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- The original walking-isomorphism evaluation has weak strict diagonal,
for any injectively fibrant ordinary Segal space. -/
theorem edgeEvaluation_diagonal_weak (W : OrdinaryCSSLocalization.Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) :
    WeakEquivalence (diagonal (OrdinarySegalWalkingEvaluation.edgeEvaluation W)) := by
  exact diagonal_weak_of_trivialFibration_mono
    (OrdinarySegalWalkingEvaluation.edgeEvaluation W)
    (OrdinarySegalCoherentArrowImage.coherentEvaluation W)
    (OrdinarySegalCoherentArrowImage.coherentArrowSubcomplex W).ι
    (OrdinarySegalCoherentArrowImage.coherentEvaluation_inclusion W)
    (OrdinarySegalCoherentEvaluationTrivialFibration.coherentEvaluation_trivialFibration
      W hSegal)

#print axioms selfPullback_of_mono_factor
#print axioms diagonal_weak_of_trivialFibration_mono
#print axioms edgeEvaluation_diagonal_weak

end
end DaggerModels.PartII.KanHomotopyMonomorphism
