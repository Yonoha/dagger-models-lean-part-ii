import DaggerModelsPartII.AdjunctionUnitCorners
import Mathlib.AlgebraicTopology.ModelCategory.Basic
import Mathlib.AlgebraicTopology.ModelCategory.Instances

/-!
# Extending the unit-corner lifting check from generators

The right mate converts each unit-corner lifting problem to a lifting problem
for its source arrow. The double orthogonal of the generator class therefore
suffices; no transfinite weak-equivalence comparison is assumed.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

namespace DaggerModels.PartII.UnitCornerClosure

open AdjunctionUnitCorners

universe u v

variable {C : Type u} {D : Type v} [Category C] [Category D]
  [HasPushouts C] [HasPullbacks C] [ModelCategory C]
  {L : C ⥤ D} {R : D ⥤ C} {S : C ⥤ D}
  (adjLR : L ⊣ R) (adjRS : R ⊣ S)

include adjRS in
/-- Local triviality of unit corners extends from I to its double
lifting-orthogonal, using only the right-mate corner correspondence. -/
theorem unitCorner_trivial_of_generators
    (I : MorphismProperty C)
    (hgen : ∀ {A B : C} (i : A ⟶ B), I i →
      trivialCofibrations C (unitPushoutCorner adjLR i).ι)
    {X Y : C} (f : X ⟶ Y) (hf : I.rlp.llp f) :
    trivialCofibrations C (unitPushoutCorner adjLR f).ι := by
  rw [← fibrations_llp]
  intro A B p hp
  have hr : I.rlp (matePullbackCorner adjLR adjRS p).π := by
    intro U V i hi
    apply (unitPushoutCorner_hasLiftingProperty_iff adjLR adjRS i p).mp
    have hg : (fibrations C).llp (unitPushoutCorner adjLR i).ι := by
      rw [fibrations_llp]
      exact hgen i hi
    exact hg p hp
  exact (unitPushoutCorner_hasLiftingProperty_iff adjLR adjRS f p).mpr (hf _ hr)

end DaggerModels.PartII.UnitCornerClosure
