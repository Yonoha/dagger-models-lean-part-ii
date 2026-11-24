import DaggerModelsPartII.FiniteFactorContractibility
import DaggerModelsPartII.JTRezkRecognition

/-! A finite-subcomplex criterion for the original fixed-target comma nerves. -/

set_option autoImplicit false

namespace DaggerModels.PartII.JTRezkRecognitionFiniteFactor

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerModels DaggerChosenRigidificationNecklace
open DaggerOriginalProductGadget DaggerSSetGluing
open scoped SSet.modelCategoryQuillen
open SegalLocalizers
open JTProjectiveOrderedFiberComparison (row)
open FiniteFactorContractibility (point_GW_of_finite_nullhomotopy)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

local instance : ModelCategory Source := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ

private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)

private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

private abbrev targetNerve (W : Source) (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
    (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)) :=
  nerve (CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y) Q)

/-- Finite subcomplexes of the original fixed-target comma nerves suffice
for the weak contractibility input of Theorem C. -/
def TargetCommaFiniteNullhomotopies : Prop :=
  ∀ (W : Source), Localization.localObject SegalLocalizers.localizingFamily W →
    ∀ (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
      (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
      (A : (targetNerve W x y Q).Subcomplex), A.toSSet.IsFinite →
      ∃ v : (Δ[0] : SSet.{0}) ⟶ targetNerve W x y Q,
        Nonempty (SSet.Homotopy
          (TopCat.toSSet.map (SSet.toTop.map A.ι))
          (TopCat.toSSet.map
            (SSet.toTop.map (SSet.stdSimplex.isTerminalObj₀.from A.toSSet ≫ v))))

/-- Apply the finite-subcomplex criterion to the same original comma nerves
and close the original four-link conclusion from that input. -/
theorem theoremC_of_finite_comma_nullhomotopies (h : TargetCommaFiniteNullhomotopies) :
    TheoremCStatement.statement := by
  apply JTRezkRecognition.theoremC_of_targetCommas
  intro W hW x y Q
  let X := targetNerve W x y Q
  let i := SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso pointIsTerminal
  have hp : SSet.stdSimplex.isTerminalObj₀.from X ≫ i.hom = pointMap X :=
    pointIsTerminal.hom_ext _ _
  haveI : WeakEquivalence (SSet.stdSimplex.isTerminalObj₀.from X) :=
    (weakEquivalence_iff_GW _).mpr (point_GW_of_finite_nullhomotopy X (h W hW x y Q))
  rw [← weakEquivalence_iff_GW]
  change WeakEquivalence (pointMap X)
  rw [← hp]
  infer_instance

end

end DaggerModels.PartII.JTRezkRecognitionFiniteFactor
