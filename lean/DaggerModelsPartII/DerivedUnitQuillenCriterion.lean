import TopCatModelCategory.QuillenAdjunction
import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma
import Mathlib.CategoryTheory.LiftingProperties.Basic

/-!
# A derived-unit criterion for a Quillen equivalence

For a Quillen adjunction, it suffices that the right adjoint reflect weak
equivalences between fibrant objects and that the unit followed by the chosen
trivial-cofibration fibrant replacement be a weak equivalence on cofibrant objects.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

universe u v

namespace DaggerModels.PartII.DerivedUnitQuillenCriterion

noncomputable section

variable {C : Type u} {D : Type v} [Category C] [Category D]
  [ModelCategory C] [ModelCategory D] (F : C ⥤ D) (G : D ⥤ C)

/-- The fixed trivial-cofibration fibrant replacement of the left adjoint's value. -/
def replacementData (A : C) :=
  MorphismProperty.factorizationData
    (trivialCofibrations D) (fibrations D) (terminal.from (F.obj A))

def derivedUnit (adj : F ⊣ G) (A : C) :
    A ⟶ G.obj ((replacementData F A).Z) :=
  adj.unit.app A ≫ G.map (replacementData F A).i

private theorem preservesWeakEquivalence_between_fibrant
    (adj : F ⊣ G) (hQ : adj.IsQuillenAdjunction)
    {X Y : D} [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y)
    [WeakEquivalence f] : WeakEquivalence (G.map f) := by
  letI : adj.IsQuillenAdjunction := hQ
  letI : G.PreservesTrivialFibrations :=
    Adjunction.IsQuillenAdjunction.preservesTrivialFibrations adj
  let b : FibrantBrownFactorization f := Classical.choice inferInstance
  haveI : Fibration b.p := (fibration_iff _).mpr b.hp
  haveI : WeakEquivalence b.p := inferInstance
  haveI : WeakEquivalence b.r := inferInstance
  haveI : WeakEquivalence (G.map b.p) := inferInstance
  haveI : WeakEquivalence (G.map b.r) := inferInstance
  have hbr : G.map b.i ≫ G.map b.r = 𝟙 (G.obj X) := by
    rw [← G.map_comp, b.i_r, G.map_id]
  have hi : WeakEquivalence (G.map b.i) := by
    exact weakEquivalence_of_postcomp_of_fac hbr
  rw [← b.fac, G.map_comp]
  infer_instance

/-- Derived-unit and fibrant-reflection criterion, with the replacement fixed by
`replacementData`. This is a reusable model-category theorem, not a verification
of its hypotheses for any particular adjunction. -/
theorem isQuillenEquivalence_of_derivedUnit_and_reflection
    (adj : F ⊣ G) (hQ : adj.IsQuillenAdjunction)
    (href : ∀ {X Y : D} [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y),
      WeakEquivalence (G.map f) → WeakEquivalence f)
    (hunit : ∀ (A : C) [IsCofibrant A], WeakEquivalence (derivedUnit F G adj A)) :
    adj.IsQuillenEquivalence := by
  refine { toIsQuillenAdjunction := hQ, weakEquivalence_homEquiv_iff := ?_ }
  intro A X hA hX f
  let d := replacementData F A
  haveI : IsFibrant d.Z := by
    change Fibration (terminal.from d.Z)
    have heq : d.p = terminal.from d.Z := terminalIsTerminal.hom_ext _ _
    rw [← heq]
    exact (fibration_iff _).mpr d.hp
  haveI : Cofibration d.i := (cofibration_iff _).mpr d.hi.1
  haveI : WeakEquivalence d.i := (weakEquivalence_iff _).mpr d.hi.2
  let sq : CommSq f d.i (terminal.from X) d.p := CommSq.mk (by
    rw [d.fac]
    exact terminalIsTerminal.hom_ext _ _)
  letI : HasLiftingProperty d.i (terminal.from X) := inferInstance
  let g : d.Z ⟶ X := sq.lift
  have hfg : d.i ≫ g = f := sq.fac_left
  have hmate : (adj.homEquiv A X) f = derivedUnit F G adj A ≫ G.map g := by
    rw [Adjunction.homEquiv_unit, ← hfg, G.map_comp]
    simp only [derivedUnit, d, Category.assoc]
  rw [hmate]
  haveI : WeakEquivalence (derivedUnit F G adj A) := hunit A
  constructor
  · intro hm
    letI : WeakEquivalence (derivedUnit F G adj A ≫ G.map g) := hm
    have hGg : WeakEquivalence (G.map g) :=
      weakEquivalence_of_precomp (derivedUnit F G adj A) (G.map g)
    have hg : WeakEquivalence g := href g hGg
    rw [← hfg]
    infer_instance
  · intro hf
    haveI : WeakEquivalence f := hf
    haveI : WeakEquivalence g := weakEquivalence_of_precomp_of_fac hfg
    haveI : WeakEquivalence (G.map g) :=
      preservesWeakEquivalence_between_fibrant F G adj hQ g
    infer_instance

end

end DaggerModels.PartII.DerivedUnitQuillenCriterion
