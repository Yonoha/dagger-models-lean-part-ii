import DaggerModelsPartII.JTWeightedComparisonWeak
import DaggerModelsPartII.JTFrameQuillen
import DaggerModelsPartII.DaggerOrdinaryDwyerKan
import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma

/-!
# Homotopical preservation by the actual vertical JT weights

The original free Gamma adjunction preserves trivial cofibrations. Native
Brown factorization extends this to all Kan weak maps of scalar simplicial
sets. The literal all-weight capital Lambda comparison then transfers weak
preservation to the free Xi realization and its canonical weighted form.
No preservation on arbitrary outer diagrams or weak density is asserted.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra DaggerModels
open DaggerUnitaryInvariance
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTWeightedWeakPreservation

open JTProjectiveGeneratorRealization

noncomputable section

private local instance : ModelCategory DaggerSimplicialCat.{0, 0} :=
  DaggerActualRigidificationQuillen.modelG.{0}

private abbrev gammaFree (m : ReverseSimplex) :=
  outerFree m ⋙ JTFrameAdjunction.frameRealization

private abbrev xiFree (m : ReverseSimplex) :=
  outerFree m ⋙ (DaggerJTRealization.daggerRealization ⋙
    OrdinaryRigidification.DaggerRigidification.daggerRigidification)

private theorem gammaFree_preservesTrivialCofibrations (m : ReverseSimplex) :
    (gammaFree m).PreservesTrivialCofibrations := by
  let R := JTFrameAdjunction.frameNerve ⋙
    (evaluation ReverseSimplexᵒᵖ SSet.{0}).obj (Opposite.op m)
  have hR : R.PreservesFibrations := by
    constructor
    intro X Y p hp
    apply (fibration_iff _).2
    change fibrations SSet.{0}
      ((JTFrameAdjunction.frameNerve.map p).app (Opposite.op m))
    exact ((fibrations SSet.{0}).arrow_mk_iso_iff
      (JTFrameQuillen.frameNerveEvaluationArrowIso m p)).2
        (JTFrameQuillen.mappingNerve_map_fibration m p ((fibration_iff p).1 hp))
  exact (gammaFreeAdjunction m).preservesTrivialCofibrations_iff_preservesFibrations.2 hR

private theorem gammaFree_map_weak (m : ReverseSimplex)
    {K L : SSet.{0}} (f : K ⟶ L) (hf : DaggerSSetGluing.GW f) :
    weakEquivalences DaggerSimplicialCat.{0, 0} ((gammaFree m).map f) := by
  have : WeakEquivalence f := (DaggerSSetGluing.weakEquivalence_iff_GW f).2 hf
  let d := (inferInstance : Nonempty (CofibrantBrownFactorization f)).some
  have hTC := gammaFree_preservesTrivialCofibrations m
  have hi := hTC.trivialCofibrations_le d.i (mem_trivialCofibrations d.i)
  have hs := hTC.trivialCofibrations_le d.s (mem_trivialCofibrations d.s)
  let P := weakEquivalences DaggerSimplicialCat.{0, 0}
  have hp : P ((gammaFree m).map d.p) := by
    apply P.of_precomp ((gammaFree m).map d.s) _ hs.2
    rw [← (gammaFree m).map_comp, d.s_p, (gammaFree m).map_id]
    exact P.id_mem _
  rw [← d.fac, Functor.map_comp]
  exact P.comp_mem _ _ hi.2 hp

/-- The actual free Gamma realization preserves every scalar Kan weak map. -/
theorem gammaFree_map_daggerDK (m : ReverseSimplex)
    {K L : SSet.{0}} (f : K ⟶ L) (hf : DaggerSSetGluing.GW f) :
    DaggerGlobalDK.daggerDK standardReplacement
      (JTFrameAdjunction.frameRealization.map ((outerFree m).map f)) := by
  rw [← DaggerActualRigidificationQuillen.target_weak]
  exact gammaFree_map_weak m f hf

/-- Naturality of the literal all-weight comparison transfers Kan weak
preservation to the original free Xi realization. -/
theorem xiFree_map_daggerDK (m : ReverseSimplex)
    {K L : SSet.{0}} (f : K ⟶ L) (hf : DaggerSSetGluing.GW f) :
    DaggerGlobalDK.daggerDK standardReplacement ((xiFree m).map f) := by
  let P := weakEquivalences DaggerSimplicialCat.{0, 0}
  have hK : P ((actualFreeComparison m).app K) := by
    change weakEquivalences DaggerSimplicialCat.{0, 0} ((actualFreeComparison m).app K)
    rw [DaggerActualRigidificationQuillen.target_weak]
    exact JTWeightedComparisonWeak.actualFreeComparison_daggerDK m K
  have hL : P ((actualFreeComparison m).app L) := by
    change weakEquivalences DaggerSimplicialCat.{0, 0} ((actualFreeComparison m).app L)
    rw [DaggerActualRigidificationQuillen.target_weak]
    exact JTWeightedComparisonWeak.actualFreeComparison_daggerDK m L
  have hComposite : P ((actualFreeComparison m).app K ≫ (xiFree m).map f) := by
    rw [← (actualFreeComparison m).naturality f]
    exact P.comp_mem _ _ (gammaFree_map_weak m f hf) hL
  rw [← DaggerActualRigidificationQuillen.target_weak]
  exact P.of_precomp _ _ hK hComposite

/-- The canonical free-weight isomorphism gives the same weak preservation
for the actual Yoneda-weighted Xi frame, with arbitrary scalar endpoints. -/
theorem xiWeighted_map_daggerDK (m : ReverseSimplex)
    {K L : SSet.{0}} (f : K ⟶ L) (hf : DaggerSSetGluing.GW f) :
    DaggerGlobalDK.daggerDK standardReplacement ((xiWeighted m).map f) := by
  let P := weakEquivalences DaggerSimplicialCat.{0, 0}
  let e : Arrow.mk ((xiFree m).map f) ≅ Arrow.mk ((xiWeighted m).map f) :=
    Arrow.isoMk ((xiFreeWeightedIso m).app K) ((xiFreeWeightedIso m).app L)
      ((xiFreeWeightedIso m).hom.naturality f).symm
  rw [← DaggerActualRigidificationQuillen.target_weak]
  apply (P.arrow_mk_iso_iff e).1
  change weakEquivalences DaggerSimplicialCat.{0, 0} ((xiFree m).map f)
  rw [DaggerActualRigidificationQuillen.target_weak]
  exact xiFree_map_daggerDK m f hf

/-- Forgetting the proven dagger condition retains the full ordinary DK
condition on the same actual weighted map. -/
theorem xiWeighted_map_W (m : ReverseSimplex)
    {K L : SSet.{0}} (f : K ⟶ L) (hf : DaggerSSetGluing.GW f) :
    OrdinaryDwyerKanCore.W
      (DaggerSimplicialCat.forget.map ((xiWeighted m).map f)) :=
  DaggerOrdinaryDwyerKan.daggerDK_forget_W standardReplacement _
    (xiWeighted_map_daggerDK m f hf)

end

end DaggerModels.PartII.JTWeightedWeakPreservation
