import OrdinaryJTArrowTensor
import OrdinaryJTMappingFrameWeak
import ReedyTerminalMatching
import DaggerModelsPartII.ReedyCoefficientChange

/-!
# Relative Reedy cofibrations of ordinary JT mapping frames

For every monomorphism of simplicial sets, the literal map between its two
ordinary JT tensor frames is a relative Reedy cofibration in the opposite
original Joyal model. The proof uses the absolute matching comparison of the
parameter and the projective Arrow corner interchange.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
  HomotopicalAlgebra MorphismProperty DaggerModels

namespace DaggerModels.PartII.OrdinaryJTRelativeMappingFrame

noncomputable section

open GroupoidSimplex JTParameterLatchingMono

private def ordinaryJoyalModel : ModelCategory SSet.{0} :=
  DaggerActualDCHRightInducedAndMainTheoremD.ordinaryJoyalModel.{0}

private local instance : ModelCategory SSet.{0} := ordinaryJoyalModel

private local instance {A B : SSet.{0}} (u : A ⟶ B) :
    PreservesLimitsOfSize.{0, 0} (JTOrdinaryEndpointFibration.tensorArrowFunctor u).op :=
  preservesLimitsOfSize_op (JTOrdinaryEndpointFibration.tensorArrowFunctor u)

private def projectiveOpp : MorphismProperty (Arrow SSet.{0})ᵒᵖ :=
  (ProjectiveArrowFactorization.projectiveArrowCofibrations
    (C := SSet.{0})).op

private local instance : projectiveOpp.RespectsIso := by
  letI := ProjectiveArrowFactorization.projectiveArrowWfs (C := SSet.{0})
  dsimp only [projectiveOpp]
  infer_instance

private theorem scalar_matching_mono (n : ℕ) :
    Mono (((matchingComparison n).app parameter.op).unop) := by
  let P := (monomorphisms SSet.{0}).op
  have hface : P ((faceLatchingMap n).op) := by
    change Mono (faceLatchingMap n)
    exact faceLatchingMap_mono n
  rw [← JTXiOrdinaryLatching.parameterMatchingIso_comp n] at hface
  have hscalar := (P.cancel_right_of_respectsIso
    ((matchingComparison n).app parameter.op)
    (JTXiOrdinaryLatching.parameterMatchingIso n).hom).mp hface
  change Mono (((matchingComparison n).app parameter.op).unop) at hscalar
  exact hscalar

private def arrowDiagram {A B : SSet.{0}} (u : A ⟶ B) :
    SimplexCategoryᵒᵖ ⥤ (Arrow SSet.{0})ᵒᵖ :=
  parameter.op ⋙ (JTOrdinaryEndpointFibration.tensorArrowFunctor u).op

private theorem absolute_matching_projective {A B : SSet.{0}}
    (u : A ⟶ B) [Mono u] (n : ℕ) :
    projectiveOpp ((matchingComparison n).app (arrowDiagram u)) := by
  let G := (JTOrdinaryEndpointFibration.tensorArrowFunctor u).op
  let c := (matchingComparison n).app parameter.op
  let e := ReedyCoefficientChange.matchingObjectIso G n parameter.op
  have hc : projectiveOpp (G.map c) := by
    change ProjectiveArrowFactorization.projectiveArrowCofibrations
      ((JTOrdinaryEndpointFibration.tensorArrowFunctor u).map c.unop)
    letI : Mono c.unop := scalar_matching_mono n
    exact OrdinaryJTArrowTensor.projective_of_mono u c.unop
  have hcomp : G.map c ≫ e.hom =
      (matchingComparison n).app (arrowDiagram u) := by
    exact ReedyCoefficientChange.matchingComparison_map G n parameter.op
  rw [← hcomp]
  exact (projectiveOpp.cancel_right_of_respectsIso (G.map c) e.hom).mpr hc

private theorem terminal_matching_projective {A B : SSet.{0}}
    (u : A ⟶ B) [Mono u] (n : ℕ) :
    ProjectiveArrowFactorization.projectiveArrowCofibrations
      ((relativeMatchingMap n (terminal.from (arrowDiagram u))).unop) := by
  have h := (projectiveOpp.arrow_mk_iso_iff
    (ReedyTerminalMatching.terminalMatchingArrowIso (arrowDiagram u) n)).2
      (absolute_matching_projective u n)
  exact h

/-- A mono of simplicial sets induces a relative Reedy cofibration of the
full ordinary JT tensor frames, in every degree including zero. -/
theorem frameMap_relativeCofibration {A B : SSet.{0}}
    (u : A ⟶ B) [Mono u] (n : ℕ) :
    cofibrations SSet.{0}
      ((relativeMatchingMap n
        (NatTrans.op (OrdinaryJTMappingFrameWeak.frameMap u))).unop) := by
  have h := ArrowReedyCornerInterchange.structure_relativeCofibration
    (arrowDiagram u) (terminal_matching_projective u) n
  change cofibrations SSet.{0}
    ((relativeMatchingMap n
      (NatTrans.op (OrdinaryJTMappingFrameWeak.frameMap u))).unop) at h
  exact h

#print axioms frameMap_relativeCofibration

end

end DaggerModels.PartII.OrdinaryJTRelativeMappingFrame
