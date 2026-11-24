import DaggerModelsPartII.JTRezkRecognitionFiniteFactor
import DaggerModelsPartII.FiniteWeakCover
import DaggerModelsPartII.JTGraphFactoredPresentation
import NerveHomotopy

/-! Weak covers of finite subcomplexes suffice for the original Theorem C. -/

set_option autoImplicit false

namespace DaggerModels.PartII.JTRezkRecognitionFiniteWeakCover

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerModels DaggerChosenRigidificationNecklace DaggerSSetGluing
open JTGraphFactoredPresentation (TargetComma)
open JTProjectiveOrderedFiberComparison (row)
open DaggerNerveHomotopy (R)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

local instance : ModelCategory Source := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ

private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)

private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

/-- The nullhomotopy requirement can be checked on weak covers of the finite
subcomplexes of the same original fixed-target comma nerves. -/
def TargetCommaFiniteWeakCovers : Prop :=
  ∀ (W : Source), Localization.localObject SegalLocalizers.localizingFamily W →
    ∀ (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
      (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
      (A : (nerve (TargetComma Q)).Subcomplex), A.toSSet.IsFinite →
      ∃ (K : SSet.{0}) (p : K ⟶ A.toSSet) (_ : WeakEquivalence p)
        (v : (Δ[0] : SSet.{0}) ⟶ nerve (TargetComma Q)),
        Nonempty (SSet.Homotopy (R.map (p ≫ A.ι))
          (R.map (p ≫ SSet.stdSimplex.isTerminalObj₀.from A.toSSet ≫ v)))

/-- Produce the original four-link conclusion from nullhomotopies on finite weak covers. -/
theorem theoremC_of_finite_weak_covers (h : TargetCommaFiniteWeakCovers) :
    TheoremCStatement.statement := by
  apply JTRezkRecognitionFiniteFactor.theoremC_of_finite_comma_nullhomotopies
  intro W hW x y Q A hA
  obtain ⟨K, p, hp, v, ⟨H⟩⟩ := h W hW x y Q A hA
  have : WeakEquivalence (R.map p) := FiniteWeakCover.weak_singular p
  refine ⟨v, ⟨FiniteWeakCover.homotopyOfPrecomp (R.map p) ?_⟩⟩
  simpa only [Functor.map_comp] using H

end

end DaggerModels.PartII.JTRezkRecognitionFiniteWeakCover
