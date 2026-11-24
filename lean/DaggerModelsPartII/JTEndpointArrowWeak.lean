import DaggerModelsPartII.JTEndpointArrowReplacement
import DaggerModelsPartII.JTWeightedComparisonWeak
import DaggerModelsPartII.JTRelativeReedyFrameProperties
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Weakness of the literal ordered endpoint comparison

The source of the endpoint arrow is the coproduct of two copies of the
outer-zero frame. The literal all-weight comparison at the coproduct of two
represented simplices identifies with its actual source component. This
uses the original dagger weak-equivalence class and does not require the
individual Xi components to be cofibrant.
-/

set_option autoImplicit false

open CategoryTheory Limits Simplicial HomotopicalAlgebra DaggerModels

namespace DaggerModels.PartII.JTEndpointArrowWeak

open JTProjectiveGeneratorRealization
open JTRelativeReedyFrame JTEndpointMateUnder JTZeroObjects JTOrderedFrameMate
open JTEndpointArrowReplacement

noncomputable section

private local instance : HasColimits Coefficient := daggerSimplicialCatHasColimits
private local instance : ModelCategory Coefficient :=
  DaggerActualRigidificationQuillen.modelG.{0}

private abbrev gammaFree (m : ReverseSimplex) :=
  outerFree m ⋙ JTFrameAdjunction.frameRealization

private abbrev xiFree (m : ReverseSimplex) :=
  outerFree m ⋙ (DaggerJTRealization.daggerRealization ⋙
    OrdinaryRigidification.DaggerRigidification.daggerRigidification)

private def gammaCoprodIso (m : ReverseSimplex) (k : SimplexCategory) :
    (GammaOuter.obj m).obj k ⨿ (GammaOuter.obj m).obj k ≅
      (gammaFree m).obj
        (SSet.stdSimplex.obj k ⨿ SSet.stdSimplex.obj k) := by
  letI : PreservesColimitsOfSize.{0, 0} (gammaFree m) :=
    (gammaFreeAdjunction m).leftAdjoint_preservesColimits
  exact coprod.mapIso (gammaRepresentedFreeIso m k)
    (gammaRepresentedFreeIso m k) ≪≫
      PreservesColimitPair.iso (gammaFree m)
        (SSet.stdSimplex.obj k) (SSet.stdSimplex.obj k)

private def xiCoprodIso (m : ReverseSimplex) (k : SimplexCategory) :
    (xiVertical m).obj k ⨿ (xiVertical m).obj k ≅
      (xiFree m).obj
        (SSet.stdSimplex.obj k ⨿ SSet.stdSimplex.obj k) := by
  letI : PreservesColimitsOfSize.{0, 0} (xiFree m) :=
    (xiFreeAdjunction m).leftAdjoint_preservesColimits
  exact coprod.mapIso (xiRepresentedFreeIso m k)
    (xiRepresentedFreeIso m k) ≪≫
      PreservesColimitPair.iso (xiFree m)
        (SSet.stdSimplex.obj k) (SSet.stdSimplex.obj k)

private theorem comparison_coprod_calibration
    (m : ReverseSimplex) (k : SimplexCategory) :
    (gammaCoprodIso m k).hom ≫
        (actualFreeComparison m).app
          (SSet.stdSimplex.obj k ⨿ SSet.stdSimplex.obj k) =
      coprod.map (JTCoendComparison.parameterComparison.app (m, k))
          (JTCoendComparison.parameterComparison.app (m, k)) ≫
        (xiCoprodIso m k).hom := by
  apply coprod.hom_ext
  · simp only [gammaCoprodIso, xiCoprodIso, Iso.trans_hom,
      coprod.mapIso_hom, PreservesColimitPair.iso_hom, Category.assoc,
      coprod.inl_map_assoc, coprodComparison_inl_assoc]
    rw [(actualFreeComparison m).naturality coprod.inl,
      coprodComparison_inl]
    simpa only [← Category.assoc] using
      congrArg (fun f ↦ f ≫ (xiFree m).map coprod.inl)
        (actualFreeComparison_represented m k)
  · simp only [gammaCoprodIso, xiCoprodIso, Iso.trans_hom,
      coprod.mapIso_hom, PreservesColimitPair.iso_hom, Category.assoc,
      coprod.inr_map_assoc, coprodComparison_inr_assoc]
    rw [(actualFreeComparison m).naturality coprod.inr,
      coprodComparison_inr]
    simpa only [← Category.assoc] using
      congrArg (fun f ↦ f ≫ (xiFree m).map coprod.inr)
        (actualFreeComparison_represented m k)

private theorem comparison_coprod_weak
    (m : ReverseSimplex) (k : SimplexCategory) :
    weakEquivalences Coefficient
      (coprod.map (JTCoendComparison.parameterComparison.app (m, k))
        (JTCoendComparison.parameterComparison.app (m, k))) := by
  let e : Arrow.mk
      (coprod.map (JTCoendComparison.parameterComparison.app (m, k))
        (JTCoendComparison.parameterComparison.app (m, k))) ≅
      Arrow.mk ((actualFreeComparison m).app
        (SSet.stdSimplex.obj k ⨿ SSet.stdSimplex.obj k)) :=
    Arrow.isoMk (gammaCoprodIso m k) (xiCoprodIso m k)
      (comparison_coprod_calibration m k)
  apply ((weakEquivalences Coefficient).arrow_mk_iso_iff e).2
  change weakEquivalences Coefficient
    (JTCoendComparison.comparison.app
      ((outerFree m).obj (SSet.stdSimplex.obj k ⨿ SSet.stdSimplex.obj k)))
  rw [DaggerActualRigidificationQuillen.target_weak]
  exact JTWeightedComparisonWeak.actualFreeComparison_daggerDK m
    (SSet.stdSimplex.obj k ⨿ SSet.stdSimplex.obj k)

/-- The source component of the literal ordered endpoint comparison is weak
in the original dagger simplicial-category model, in every simplex degree. -/
theorem comparisonSource_weak (k : SimplexCategory) :
    weakEquivalences Coefficient (comparisonSource.app k) := by
  change weakEquivalences Coefficient
    (coprod.map ((comparison.app k).app zeroIndex)
      ((comparison.app k).app zeroIndex))
  simpa only [JTCoendComparison.parameterComparison_app] using
    comparison_coprod_weak zeroIndex k

/-- The target component is the existing componentwise weak equivalence
of the original full-outer comparison. -/
theorem comparisonOne_weak (k : SimplexCategory) :
    weakEquivalences Coefficient (comparisonOne.app k) := by
  induction k using SimplexCategory.rec with | h n =>
    change weakEquivalences Coefficient ((comparison.app ⦋n⦌).app oneIndex)
    exact JTRelativeReedyFrame.comparison_component_weak oneIndex n

/-- The actual Gamma-to-Xi comparison of ordered arrows is weak on both
its source and target, at every cosimplicial degree. -/
theorem lambda_pointwiseWeak (n : ℕ) :
    weakEquivalences Coefficient (lambda.app ⦋n⦌).left ∧
      weakEquivalences Coefficient (lambda.app ⦋n⦌).right := by
  exact ⟨comparisonSource_weak ⦋n⦌, comparisonOne_weak ⦋n⦌⟩

/-- The literal comparison between the two zero-fixed Reedy replacements
is weak on both components in every degree. The checked replacement maps
and the original comparison square supply the two-out-of-three step. -/
theorem Qlambda_pointwiseWeak (n : ℕ) :
    weakEquivalences Coefficient (Qlambda.app ⦋n⦌).left ∧
      weakEquivalences Coefficient (Qlambda.app ⦋n⦌).right := by
  let P := weakEquivalences Coefficient
  have hleft := congrArg (fun t : QG ⟶ X ↦ (t.app ⦋n⦌).left) Qlambda_square
  change (Qlambda.app ⦋n⦌).left ≫ (qX.app ⦋n⦌).left =
    (qG.app ⦋n⦌).left ≫ (lambda.app ⦋n⦌).left at hleft
  have hright := congrArg (fun t : QG ⟶ X ↦ (t.app ⦋n⦌).right) Qlambda_square
  change (Qlambda.app ⦋n⦌).right ≫ (qX.app ⦋n⦌).right =
    (qG.app ⦋n⦌).right ≫ (lambda.app ⦋n⦌).right at hright
  constructor
  · have hcomp : P
        ((Qlambda.app ⦋n⦌).left ≫ (qX.app ⦋n⦌).left) := by
      rw [hleft]
      exact P.comp_mem _ _ (qG_pointwiseWeak n).1 (lambda_pointwiseWeak n).1
    exact P.of_postcomp _ _ (qX_pointwiseWeak n).1 hcomp
  · have hcomp : P
        ((Qlambda.app ⦋n⦌).right ≫ (qX.app ⦋n⦌).right) := by
      rw [hright]
      exact P.comp_mem _ _ (qG_pointwiseWeak n).2 (lambda_pointwiseWeak n).2
    exact P.of_postcomp _ _ (qX_pointwiseWeak n).2 hcomp

end

end DaggerModels.PartII.JTEndpointArrowWeak
