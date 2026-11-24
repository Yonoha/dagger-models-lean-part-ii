import NativeSSetFibrationSquareFibreWeak

/-!
# A chosen homotopy fiber compared with an actual fibration model

Factor the original arrow by a trivial cofibration and a fibration without
changing its base. A weak square to an actual fibration yields a weak map
from this chosen fiber model to the target's strict fiber. The comparison
uses the original point and square, not an assumption that the raw arrow
is already a fibration.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.ChosenHomotopyFiberComparison

noncomputable section

/-- The actual original-arrow factorization keeps its base unchanged. -/
def replacement {X B : SSet.{u}} (p : X ⟶ B) :=
  factorizationData (trivialCofibrations SSet.{u}) (fibrations SSet.{u}) p

/-- The chosen fiber of the fibration replacement over the specified point. -/
def chosenFiber {X B K : SSet.{u}} (p : X ⟶ B) (b : K ⟶ B) : SSet.{u} :=
  pullback (replacement p).p b

section Comparison

variable {X Y B D K : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ D)
  (f : X ⟶ Y) (g : B ⟶ D) (h : p ≫ g = f ≫ q) [Fibration q]

private def comparisonSquare :
    CommSq f (replacement p).i q ((replacement p).p ≫ g) := by
  constructor
  rw [← Category.assoc, (replacement p).fac]
  exact h.symm

/-- Extend the original total map across the chosen trivial cofibration. -/
def comparisonTotal : (replacement p).Z ⟶ Y := by
  haveI : Cofibration (replacement p).i :=
    (cofibration_iff _).mpr (replacement p).hi.1
  haveI : WeakEquivalence (replacement p).i :=
    (weakEquivalence_iff _).mpr (replacement p).hi.2
  exact (comparisonSquare p q f g h).lift

/-- The extension restricts to the original total map. -/
theorem replacement_i_comparisonTotal :
    (replacement p).i ≫ comparisonTotal p q f g h = f := by
  haveI : Cofibration (replacement p).i :=
    (cofibration_iff _).mpr (replacement p).hi.1
  haveI : WeakEquivalence (replacement p).i :=
    (weakEquivalence_iff _).mpr (replacement p).hi.2
  exact (comparisonSquare p q f g h).fac_left

/-- The extension retains the original map of bases. -/
theorem comparisonTotal_projection :
    comparisonTotal p q f g h ≫ q = (replacement p).p ≫ g := by
  haveI : Cofibration (replacement p).i :=
    (cofibration_iff _).mpr (replacement p).hi.1
  haveI : WeakEquivalence (replacement p).i :=
    (weakEquivalence_iff _).mpr (replacement p).hi.2
  exact (comparisonSquare p q f g h).fac_right

variable (b : K ⟶ B) (d : K ⟶ D) (hb : b ≫ g = d)

/-- The comparison from the chosen original fiber model to the strict fiber
of the supplied actual fibration. -/
def comparison : chosenFiber p b ⟶ pullback q d :=
  DaggerNativeSSetFibrationSquareFibreWeak.fibreMap
    (replacement p).p q (comparisonTotal p q f g h) g
    (comparisonTotal_projection p q f g h).symm b d hb

/-- A weak square to an actual fibration computes the same homotopy fiber.
The original projection `p` need not be a fibration. -/
theorem comparison_weak [WeakEquivalence f] [WeakEquivalence g] :
    WeakEquivalence (comparison p q f g h b d hb) := by
  haveI : Fibration (replacement p).p :=
    (fibration_iff _).mpr (replacement p).hp
  haveI : WeakEquivalence (replacement p).i :=
    (weakEquivalence_iff _).mpr (replacement p).hi.2
  haveI : WeakEquivalence (comparisonTotal p q f g h) :=
    weakEquivalence_of_precomp_of_fac (replacement_i_comparisonTotal p q f g h)
  exact DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_weakEquivalence
    (replacement p).p q (comparisonTotal p q f g h) g
      (comparisonTotal_projection p q f g h).symm b d hb

end Comparison

end

end DaggerModels.PartII.ChosenHomotopyFiberComparison
