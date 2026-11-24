import DaggerModelsPartII.SegalLocalizationModels
import DaggerModelsPartII.ActualSegalLocalization
import DaggerModelsPartII.DiagramTensorMappingAdjunction

/-!
# Theorem B: concrete statement at simplicial-set universe zero

This file states the manuscript's Theorem B for the literal reversal and
Part I dagger-simplex index categories. It packages the chosen injective and
projective localizations, their actual simplicial tensor and mapping space,
the exact fibrancy descriptions, and the change-of-index Quillen equivalence.
No proof of the final Quillen equivalence is imported here.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open DaggerModels.PartII.SegalLocalizers
open DaggerModels.PartII.ActualIndexProjectiveModel
open DaggerModels.PartII.InjectiveKanDiagram
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.TheoremBStatement

noncomputable section

/-- Left properness of the supplied model on the actual reversal diagram
category, with the weak equivalence pushed along a cofibration. -/
def leftProper (M : ModelCategory ReverseDaggerSpace.{0}) : Prop :=
  ∀ {A B D P : ReverseDaggerSpace.{0}}
    {i : A ⟶ B} {k : A ⟶ D} {l : B ⟶ P} {r : D ⟶ P},
    IsPushout i k l r →
      M.categoryWithCofibrations.cofibrations i →
        M.categoryWithWeakEquivalences.weakEquivalences k →
          M.categoryWithWeakEquivalences.weakEquivalences l

/-- The literal levelwise tensor and simplicial mapping space are adjoint;
the chosen injective Segal localization satisfies pushout-product SM7 for
this tensor and the ordinary Kan model on simplicial sets. -/
def simplicialSM7 : Prop :=
  (∀ A : ReverseDaggerSpace.{0},
      Nonempty (diagramTensor A ⊣ diagramMappingTarget A)) ∧
    ∀ {A B : ReverseDaggerSpace.{0}} (i : A ⟶ B)
      {K L : SSet.{0}} (j : K ⟶ L),
      injectiveSegalModel.categoryWithCofibrations.cofibrations i →
      HomotopicalAlgebra.cofibrations SSet.{0} j →
      ∀ sq : Functor.PushoutObjObj
        (curriedDiagramTensor ReverseSimplexᵒᵖ) i j,
        injectiveSegalModel.categoryWithCofibrations.cofibrations sq.ι ∧
          ((injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences i ∨
              HomotopicalAlgebra.weakEquivalences SSet.{0} j) →
            injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences sq.ι)

/-- Theorem B with the manuscript's actual localizing families and actual
left Kan extension–restriction adjunction, specialized to `SSet.{0}`. -/
def statement : Prop :=
  leftProper injectiveSegalModel ∧
    ModelProperties.combinatorial.{0} injectiveSegalModel ∧
    simplicialSM7 ∧
    (∀ W : ReverseDaggerSpace.{0},
      @IsFibrant ReverseDaggerSpace.{0} _
        injectiveSegalModel.categoryWithFibrations _ W ↔
        (letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ;
          IsFibrant W ∧ unitarilyCompleteSegalCondition W)) ∧
    (∀ W : ReverseDaggerSpace.{0},
      @IsFibrant ReverseDaggerSpace.{0} _
        projectiveSegalModel.categoryWithFibrations _ W ↔
          derivedUnitarilyCompleteSegalCondition W) ∧
    (∀ W : ActualSpace,
      @IsFibrant ActualSpace _ actualSegalModel.categoryWithFibrations _ W ↔
        (∀ d, IsFibrant (W.obj d)) ∧
          derivedUnitarilyCompleteSegalCondition (actualRestriction.{0}.obj W)) ∧
    @Adjunction.IsQuillenEquivalence ReverseDaggerSpace.{0} ActualSpace _ _
      projectiveSegalModel actualSegalModel
      actualLeftExtension.{0} actualRestriction.{0} actualLeftAdjunction.{0}

end

end DaggerModels.PartII.TheoremBStatement
