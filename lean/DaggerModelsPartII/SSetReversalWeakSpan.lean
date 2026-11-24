import OriginalRealizationReversalCoherence
import NativeRealEdgewiseComparisonWeakReduction

/-!
# A natural weak cospan between a simplicial set and its reversal

The existing realization/singular unit and actual realization reversal are
used literally. This supplies orientation changes, not a bar-to-elements theorem.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.SSetReversalWeakSpan

noncomputable section

/-- The original realization followed by the original singular functor. -/
def comparisonTarget : SSet.{u} ⥤ SSet.{u} := SSet.toTop ⋙ TopCat.toSSet

/-- The original realization/singular unit is one leg. -/
def forward : 𝟭 (SSet.{u}) ⟶ comparisonTarget := sSetTopAdj.unit

/-- The reversed unit followed by the actual realization reversal is the other leg. -/
def reverse : SSet.opFunctor.{u} ⟶ comparisonTarget :=
  Functor.whiskerLeft SSet.opFunctor sSetTopAdj.unit ≫
    Functor.whiskerRight
      DaggerOriginalRealizationOppositeComparison.realizationOppositeIso.hom TopCat.toSSet

/-- The forward leg is Kan weak for every original simplicial set, without fibrancy. -/
theorem forward_weak (X : SSet.{u}) : WeakEquivalence (forward.app X) := by
  change WeakEquivalence (sSetTopAdj.unit.app X)
  infer_instance

/-- The other leg is Kan weak, using an actual isomorphism after the same unit. -/
theorem reverse_weak (X : SSet.{u}) : WeakEquivalence (reverse.app X) := by
  change WeakEquivalence (sSetTopAdj.unit.app (SSet.opFunctor.obj X) ≫
    TopCat.toSSet.map
      (DaggerOriginalRealizationOppositeComparison.realizationOppositeIso.hom.app X))
  infer_instance

/-- The cospan leg is calibrated to the existing singular-reversal mate. -/
theorem reverse_mate (X : SSet.{u}) :
    reverse.app X = SSet.opFunctor.map (sSetTopAdj.unit.app X) ≫
      DaggerOriginalSingularSetReversal.singularReversal.hom.app (SSet.toTop.obj X) :=
  DaggerOriginalRealizationReversalCoherence.realization_mate X

end

end DaggerModels.PartII.SSetReversalWeakSpan
