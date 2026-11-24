import OrdinaryJTRightNerveSegal
import DaggerModelsPartII.JTParameterContraction

/-!
# The ordinary JT right nerve walking restriction

The chosen vertex of the actual groupoid-completed one-simplex is an ordinary
Joyal weak map. The mapping-frame theorem therefore makes restriction along
that vertex Kan weak into every quasicategory. The target is the literal
degree-zero row of the ordinary JT right nerve, through its native row iso.
This is the ordinary right-nerve completeness weight, not a derived-unit claim.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryJTRightNerveCompleteness

noncomputable section

private theorem iso_categorical_weak {X Y : SSet.{0}} (f : X ⟶ Y) [IsIso f] :
    DaggerNativeJoyalMappingTest.weakCategoricalEquivalences f := by
  let P := DaggerNativeJoyalMappingTest.weakCategoricalEquivalences
  let e : Arrow.mk (𝟙 X) ≅ Arrow.mk f :=
    Arrow.isoMk (Iso.refl X) (asIso f) (by simp)
  exact P.of_retract (Retract.ofIso e.symm) (P.id_mem X)

/-- The selected vertex of each actual groupoid parameter is ordinary Joyal weak. -/
theorem parameterVertex_categorical_weak (k : SimplexCategory)
    (j : Fin (k.len + 1)) :
    DaggerNativeJoyalMappingTest.weakCategoricalEquivalences
      (JTParameterContraction.parameterVertex k j) := by
  let P := DaggerNativeJoyalMappingTest.weakCategoricalEquivalences
  let v := JTParameterContraction.parameterVertex k j
  let a := terminal.from (GroupoidSimplex.parameter.obj k)
  have ha : P a :=
    (DaggerNativeJoyalFirstFactorization.kan_trivial_le_candidate_trivial a
      (GroupoidSimplex.augmentation_trivialFibration k)).2
  have h : v ≫ a = terminal.from (Δ[0] : SSet.{0}) :=
    terminalIsTerminal.hom_ext _ _
  have hcomp : P (v ≫ a) := by
    rw [h]
    have : IsIso (terminal.from (Δ[0] : SSet.{0})) := by
      let e := SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso
        (terminalIsTerminal : IsTerminal (⊤_ SSet.{0}))
      have he : terminal.from (Δ[0] : SSet.{0}) = e.hom :=
        terminalIsTerminal.hom_ext _ _
      rw [he]
      infer_instance
    exact iso_categorical_weak _
  exact P.of_postcomp v a ha hcomp

/-- Restrict the literal ordinary JT right nerve at its walking parameter
to the selected degree-zero row, without changing the ordinary target. -/
def walkingRestriction (X : SSet.{0}) :
    OrdinaryJTMappingFrameWeak.mapping X (GroupoidSimplex.parameter.obj ⦋1⦌) ⟶
      JTRightAdjointOrderedFiber.ordinaryRow X ⦋0⦌ :=
  OrdinaryJTMappingFrameWeak.restriction X
      (JTParameterContraction.parameterVertex ⦋1⦌ 0) ≫
    (OrdinaryJTRightNerveSegal.rowMappingIso X ⦋0⦌).inv

/-- The actual ordinary right-nerve walking restriction is Kan weak into
every quasicategory, with no locality hypothesis on a source diagram. -/
theorem walkingRestriction_weak (X : SSet.{0}) [X.Quasicategory] :
    DaggerSSetGluing.GW (walkingRestriction X) := by
  letI : WeakEquivalence
      (OrdinaryJTMappingFrameWeak.restriction X
        (JTParameterContraction.parameterVertex ⦋1⦌ 0)) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
      (OrdinaryJTMappingFrameWeak.restriction_weak X
        (JTParameterContraction.parameterVertex ⦋1⦌ 0)
        (parameterVertex_categorical_weak ⦋1⦌ 0))
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).mp
  change WeakEquivalence
    (OrdinaryJTMappingFrameWeak.restriction X
        (JTParameterContraction.parameterVertex ⦋1⦌ 0) ≫
      (OrdinaryJTRightNerveSegal.rowMappingIso X ⦋0⦌).inv)
  infer_instance

#print axioms parameterVertex_categorical_weak
#print axioms walkingRestriction_weak

end

end DaggerModels.PartII.OrdinaryJTRightNerveCompleteness
