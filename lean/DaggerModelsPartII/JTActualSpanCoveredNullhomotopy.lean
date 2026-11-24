import DaggerModelsPartII.JTActualSpanPrismLiftCover
import DaggerModelsPartII.FiniteSupportWeakCoverNullhomotopy

/-! A direct nullhomotopy criterion on the exact original full-prism lift cover. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerNerveHomotopy

namespace DaggerModels.PartII.JTActualSpanCoveredNullhomotopy

open JTGraphFactoredPresentation (TargetComma)
open JTProjectiveOrderedFiberComparison (row)
open JTActualSpanPrismLiftCover (Lifted projection projection_weak evaluation original_comparison)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev toPoint (X : SSet.{0}) := SSet.stdSimplex.isTerminalObj₀.from X

local instance : ModelCategory Source := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ

/-- The exact original evaluation has a nullhomotopy on each full-prism cover
of a finite-object full subcategory. No contractible category factor is required. -/
def FiniteCoveredNullhomotopies : Prop :=
  ∀ (W : Source), Localization.localObject SegalLocalizers.localizingFamily W →
    ∀ (x y : Vertex W) (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
      (A : (nerve (TargetComma Q)).Subcomplex), A.toSSet.IsFinite →
      ∀ (P : ObjectProperty (JTSemisimplicialSpanEvaluation.Presentation Q A)),
        Finite P.FullSubcategory →
        ∃ v : (Δ[0] : SSet.{0}) ⟶ nerve (TargetComma Q),
          Nonempty (SSet.Homotopy (R.map (nerveMap (evaluation Q A P)))
            (R.map (toPoint (nerve (Lifted Q A P)) ≫ v)))

/-- Covered nullhomotopies supply the finite-support condition on the exact
original span evaluation, using its checked weak projection and comparison. -/
theorem support_nullhomotopies (h : FiniteCoveredNullhomotopies) :
    JTGraphSpanSupportCriterion.FullSupportNullhomotopies := by
  intro W hW x y Q A hA
  apply FiniteLastVertexSupport.of_finite_full_weak_cover_nullhomotopies
  intro P hP
  exact ⟨Cat.of (Lifted Q A P), projection Q A P, evaluation Q A P,
    projection_weak Q A P, original_comparison Q A P, h W hW x y Q A hA P hP⟩

/-- The direct covered nullhomotopy condition implies all four links of the
unchanged original Theorem C. The condition itself remains to be proved. -/
theorem theoremC_of_covered_nullhomotopies (h : FiniteCoveredNullhomotopies) :
    TheoremCStatement.statement :=
  JTGraphSpanSupportCriterion.theoremC_of_support_nullhomotopies (support_nullhomotopies h)

end

end DaggerModels.PartII.JTActualSpanCoveredNullhomotopy
