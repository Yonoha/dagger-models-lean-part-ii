import DaggerModelsPartII.JTActualLambdaCellGluing
import DaggerModelsPartII.FiniteSubcomplexPresentation
import DaggerModelsPartII.FiniteCellBoundaryInduction
import DaggerModelsPartII.JTCoendEssentialSurjectivity

/-!
# Actual JT comparison on arbitrary free simplicial-set weights

The literal weighted comparison is weak on finite weights by boundary-cell
induction, then on all weights by the finite-subcomplex filtered colimit.
Canonical normalization transports this to the original capital Lambda on
every outer free input. The retained coherent-unitary object witness supplies
the dagger DK condition at those same inputs.
-/

set_option autoImplicit false

open CategoryTheory Limits Simplicial DaggerModels
open DaggerModels.OrdinaryDwyerKanCore
open DaggerUnitaryInvariance

namespace DaggerModels.PartII.JTWeightedComparisonWeak

open JTActualLambdaCellGluing JTProjectiveGeneratorRealization
open FiniteSubcomplexPresentation FiniteCellBoundaryInduction

noncomputable section

/-- The independently descended literal weighted comparison is ordinary DK
on every finite simplicial-set weight. -/
theorem weightedComparison_finite_W (m : ReverseSimplex) (K : SSet.{0}) [K.IsFinite] :
    W ((ordinaryWeightedComparison m).app K) := by
  apply finite_induction_with_boundary
    (fun T : SSet.{0} ↦ W ((ordinaryWeightedComparison m).app T))
  · intro T hT
    letI : T.HasDimensionLT 0 := hT
    exact weightedComparison_initial_W m T
      (SSet.isInitialOfNotNonempty
        ((SSet.notNonempty_iff_hasDimensionLT_zero T).2 inferInstance))
  · intro n
    simpa using weightedComparison_represented_W m ⦋n⦌
  · intro A X i n t b sq hA hBoundary hSimplex
    letI : Mono ((SSet.boundary n).ι : (SSet.boundary n : SSet.{0}) ⟶ Δ[n]) :=
      inferInstance
    exact weightedComparison_mono_isPushout m sq.flip hBoundary hSimplex hA

/-- Every simplicial-set weight is the filtered colimit of its actual finite
subcomplexes, so the finite comparison theorem extends without a finiteness
or cofibrancy hypothesis on K. -/
theorem weightedComparison_W (m : ReverseSimplex) (K : SSet.{0}) :
    W ((ordinaryWeightedComparison m).app K) := by
  apply weightedComparison_filtered_W m (diagram K) (cocone K) (isColimit K)
  · intro j k f
    change Mono (SSet.Subcomplex.homOfLE (show j.1 ≤ k.1 from leOfHom f))
    infer_instance
  · intro A
    letI : SSet.IsFinite (A.1 : SSet.{0}) := A.2
    exact weightedComparison_finite_W m A.1

/-- The actual capital Lambda on every outer free coefficient is ordinary DK
after forgetting dagger. The comparison remains the original capital map. -/
theorem actualFreeComparison_W (m : ReverseSimplex) (K : SSet.{0}) :
    W (DaggerSimplicialCat.forget.map ((actualFreeComparison m).app K)) := by
  have hEq := NatTrans.congr_app (actualFreeComparison_weighted m) K
  have hMap := congrArg DaggerSimplicialCat.forget.map hEq
  simp only [NatTrans.comp_app, Functor.map_comp] at hMap
  have hWeighted :
      W (DaggerSimplicialCat.forget.map ((weightedComparison m).app K)) := by
    simpa [ordinaryWeightedComparison] using weightedComparison_W m K
  have hComposite : W
      (DaggerSimplicialCat.forget.map ((actualFreeComparison m).app K) ≫
        DaggerSimplicialCat.forget.map ((xiFreeWeightedIso m).hom.app K)) := by
    rw [hMap]
    exact W.comp_mem _ _ (W.of_isIso _) hWeighted
  exact W.of_postcomp _ _ (W.of_isIso _) hComposite

/-- The literal capital Lambda is dagger DK on every outer free coefficient.
Its local part comes from the actual ordinary comparison, and its coherent
unitary essential-surjectivity witness is the existing all-input theorem. -/
theorem actualFreeComparison_daggerDK (m : ReverseSimplex) (K : SSet.{0}) :
    DaggerGlobalDK.daggerDK standardReplacement
      (JTCoendComparison.comparison.app ((outerFree m).obj K)) := by
  refine ⟨?_, JTCoendEssentialSurjectivity.comparison_ess _⟩
  have hW := actualFreeComparison_W m K
  change W (DaggerSimplicialCat.forget.map
    (JTCoendComparison.comparison.app ((outerFree m).obj K))) at hW
  intro x y
  exact hW.1 x y

end

end DaggerModels.PartII.JTWeightedComparisonWeak
