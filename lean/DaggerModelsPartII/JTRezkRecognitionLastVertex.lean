import DaggerModelsPartII.JTRezkRecognitionFiniteFactor
import DaggerModelsPartII.NerveSubcomplexLastVertexCriterion

/-! The last-vertex comparison for the original fixed-target commas. -/

set_option autoImplicit false

namespace DaggerModels.PartII.JTRezkRecognitionLastVertex

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerModels DaggerChosenRigidificationNecklace DaggerSSetGluing
open JTGraphFactoredPresentation (TargetComma)
open JTProjectiveOrderedFiberComparison (row)
open NerveSimplexResolutionHomotopy (lastVertexOnSubcomplex)
open DaggerNerveHomotopy (R)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

local instance : ModelCategory Source := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ

private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)

private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

/-- The exact last-vertex diagrams whose nullhomotopies give the original theorem. -/
def TargetCommaLastVertexNullhomotopies : Prop :=
  ∀ (W : Source), Localization.localObject SegalLocalizers.localizingFamily W →
    ∀ (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
      (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
      (A : (nerve (TargetComma Q)).Subcomplex), A.toSSet.IsFinite →
      ∃ v : (Δ[0] : SSet.{0}) ⟶ nerve (TargetComma Q),
        Nonempty (SSet.Homotopy (R.map (nerveMap (lastVertexOnSubcomplex (TargetComma Q) A)))
          (R.map (SSet.stdSimplex.isTerminalObj₀.from (nerve A.toSSet.Elementsᵒᵖ) ≫ v)))

/-- The original theorem follows from contraction on the finite last-vertex diagrams. -/
theorem theoremC_of_last_vertex (h : TargetCommaLastVertexNullhomotopies) :
    TheoremCStatement.statement := by
  apply JTRezkRecognitionFiniteFactor.theoremC_of_finite_comma_nullhomotopies
  intro W hW x y Q A hA
  obtain ⟨v, ⟨H⟩⟩ := h W hW x y Q A hA
  exact ⟨v, NerveSubcomplexLastVertexCriterion.inclusion_nullhomotopic A v H⟩

end
end DaggerModels.PartII.JTRezkRecognitionLastVertex
