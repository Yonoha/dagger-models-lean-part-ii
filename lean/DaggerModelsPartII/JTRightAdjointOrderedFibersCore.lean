import DaggerModelsPartII.JTUnderlyingRightComparison
import DaggerModelsPartII.JTCoendMateFormula
import DaggerModelsPartII.JTRealizationGenerators

/-!
# Actual underlying JT right comparison on a represented generator

This bounded leaf computes the specified transformation `vartheta` through
the original two adjunctions. Its result is precomposition by the original
ordinary coend generator associated to the represented identity. Identifying
this generator with the literal forward copy remains a separate proof.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.JTRightAdjointOrderedFibersCore

open DaggerJTAdjunction OrdinaryJTRealization JTReversalInput

noncomputable section

/-- The represented identity transported through the actual source equivalence. -/
def representedUnitCoefficient (m k : SimplexCategory) :
    (ordinaryInput.obj
      (JTCoendMateFormula.representedInput
        (ReverseSimplex.inclusion.obj m, k))).obj (op (m, k)) :=
  JTCoendMateFormula.representedEvaluation
    (JTCoendMateFormula.representedInput
      (ReverseSimplex.inclusion.obj m, k))
    (ReverseSimplex.inclusion.obj m, k) (𝟙 _)

/-- The original adjunction and represented evaluation, with both indices retained. -/
def daggerGeneratorEquiv (X : DaggerSSet.{0})
    (m : ReverseSimplex) (k : SimplexCategory) :
    (frame.obj (m, k) ⟶ X) ≃
      ((daggerNerve.obj X).obj (op m)).obj (op k) :=
  (adjunction.homEquiv
    (JTCoendMateFormula.representedInput (m, k)) X).trans
      (JTCoendMateFormula.representedEvaluation (daggerNerve.obj X) (m, k))

/-- The represented identity coefficient evaluates the actual source morphism. -/
theorem representedUnit_naturality (m k : SimplexCategory)
    {V : SegalLocalizers.ReverseDaggerSpace.{0}}
    (h : JTCoendMateFormula.representedInput
      (ReverseSimplex.inclusion.obj m, k) ⟶ V) :
    (ordinaryInput.map h).app (op (m, k))
        (representedUnitCoefficient m k) =
      JTCoendMateFormula.representedEvaluation V
        (ReverseSimplex.inclusion.obj m, k) h := by
  have q := JTCoendMateFormula.representedEvaluation_naturality
    (ReverseSimplex.inclusion.obj m, k)
      (𝟙 (JTCoendMateFormula.representedInput
        (ReverseSimplex.inclusion.obj m, k))) h
  simpa only [Category.id_comp, representedUnitCoefficient,
    JTReversalInput.ordinaryInput_map_app] using q.symm

/-- The actual ordinary realization generator of the represented identity coefficient. -/
def canonicalMateForwardUnit (m k : SimplexCategory) :
    tFunctor.obj (m, k) ⟶
      (frame.obj (ReverseSimplex.inclusion.obj m, k)).toSSet :=
  JTRealizationGenerators.generator
    (ordinaryInput.obj
      (JTCoendMateFormula.representedInput
        (ReverseSimplex.inclusion.obj m, k)))
    (m, k) (representedUnitCoefficient m k)

/-- The original ordinary adjunction evaluates as the specified coend generator. -/
theorem ordinaryAdjunction_generator (W : BiPresheaf)
    (X : SSet.{0}) (g : realization.obj W ⟶ X)
    (p : Index) (w : W.obj (op p)) :
    (((realizationNerveAdjunction.homEquiv W X g).app (op p) w).down) =
      JTRealizationGenerators.generator W p w ≫ g := by
  change (((Presheaf.uliftYonedaAdjunction realization realizationUnit).homEquiv
      W X g).app (op p) w).down = _
  rw [Presheaf.uliftYonedaAdjunction_homEquiv_app]
  rfl

/-- The original `vartheta_X` component uses the actual ordinary coend
generator, with the source element supplied by the original dagger adjunction. -/
theorem comparison_on_represented (X : DaggerSSet.{0})
    (m k : SimplexCategory)
    (f : frame.obj (ReverseSimplex.inclusion.obj m, k) ⟶ X) :
    (((JTUnderlyingRightComparison.comparison.app X).app (op (m, k)))
      (daggerGeneratorEquiv X (ReverseSimplex.inclusion.obj m) k f)).down =
        canonicalMateForwardUnit m k ≫ f.hom := by
  let W := JTCoendMateFormula.representedInput
    (ReverseSimplex.inclusion.obj m, k)
  let h : W ⟶ daggerNerve.obj X := adjunction.homEquiv W X f
  have hs := representedUnit_naturality m k h
  have hc := congrArg
    (fun t : ordinaryInput.obj W ⟶ nerve.obj X.toSSet =>
      (t.app (op (m, k)) (representedUnitCoefficient m k)).down)
    (JTUnderlyingRightComparison.homEquiv_comparison W X f)
  change (((JTUnderlyingRightComparison.comparison.app X).app (op (m, k)))
      ((ordinaryInput.map h).app (op (m, k))
        (representedUnitCoefficient m k))).down =
      (((realizationNerveAdjunction.homEquiv
        (ordinaryInput.obj W) X.toSSet (DaggerSSet.forget.map f)).app
          (op (m, k)) (representedUnitCoefficient m k)).down) at hc
  rw [hs] at hc
  change (((JTUnderlyingRightComparison.comparison.app X).app (op (m, k)))
      (daggerGeneratorEquiv X (ReverseSimplex.inclusion.obj m) k f)).down = _ at hc
  exact hc.trans (ordinaryAdjunction_generator (ordinaryInput.obj W)
    X.toSSet (DaggerSSet.forget.map f) (m, k)
      (representedUnitCoefficient m k))

end

end DaggerModels.PartII.JTRightAdjointOrderedFibersCore
