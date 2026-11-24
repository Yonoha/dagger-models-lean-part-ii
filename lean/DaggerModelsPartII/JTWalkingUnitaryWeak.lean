import DaggerModelsPartII.JTBarFunctorWeak
import DaggerModelsPartII.JTCofibrantAugmentationWeak
import DaggerModelsPartII.SegalLocalizers
import ActualDaggerQuillenEquivalenceReduction
import ActualConstantSimplicialCategory
import ActualWalkingCategoricalIntervalReversal
import OriginalGlobalFibrancyRecovered
import OriginalActualGlobalWeakPropertiesRecovered
import OriginalTaggedFreeZeroNativeWitness
import DaggerModels.DaggerDiscreteObjects

/-!
# The actual walking-unitary collapse

The collapse is fixed by the coherent nerve of the canonical functor from
the walking unitary enrichment to the original one-object dagger category.
The target is identified with the paper's free zero simplex by the existing
Part I point isomorphism.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
  Opposite Simplicial DaggerModels
open DaggerModels.OrdinaryRigidification
open DaggerModels.OrdinaryRigidification.DaggerNerve
open DaggerModels.OrdinaryRigidification.DaggerRigidification
open DaggerModels.OriginalWalkingIsoIntegerObstruction
open DaggerActualWalkingCategoricalIntervalReversal
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTWalkingUnitaryWeak

open SegalLocalizers

noncomputable section

private local instance : ModelCategory DaggerSSet.{0} :=
  DaggerActualRigidificationQuillen.modelD.{0}
private local instance : ModelCategory DaggerSimplicialCat.{0, 0} :=
  DaggerActualRigidificationQuillen.modelG.{0}
private local instance : ModelCategory ReverseDaggerSpace.{0} :=
  ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ

/-- The canonical one-object collapse of the original walking unitary
dagger simplicial category. -/
def walkingCollapse :
    DaggerUnitaryDiscrete.ordinaryEnrichment walkingIso.{0} ⟶
      DaggerDiscreteObjects.point.{0, 0} :=
  DaggerDiscreteObjects.toPoint _

/-- The coherent nerve of the original terminal dagger simplicial category
is terminal, by the fixed Part I adjunction. -/
def nervePointIsTerminal :
    IsTerminal (daggerCoherentNerve.obj DaggerDiscreteObjects.point.{0, 0}) := by
  letI : PreservesLimits daggerCoherentNerve.{0} :=
    DaggerActualRigidificationQuillen.adjunction.rightAdjoint_preservesLimits
  exact DaggerDiscreteObjects.pointIsTerminal.isTerminalObj
    daggerCoherentNerve DaggerDiscreteObjects.point

/-- The selected terminal-nerve identification lands in the paper's
literal free dagger zero-simplex. -/
def nervePointFreeZeroIso :
    daggerCoherentNerve.obj DaggerDiscreteObjects.point.{0, 0} ≅
      freeSimplex 0 :=
  nervePointIsTerminal.uniqueUpToIso DaggerSSet.pointIsTerminal ≪≫
    DaggerOriginalTaggedFreeZeroNativeWitness.pointFreeZeroIso

/-- The specified collapse `c†` from the walking-unitary nerve to the
original free zero simplex, with the coherent-nerve and terminal
identifications made explicit. -/
def collapseDagger : walkingUnitaryNerve.{0} ⟶ freeSimplex 0 :=
  walkingUnitaryCoherentNerveIso.inv ≫
    daggerCoherentNerve.map walkingCollapse ≫
      nervePointFreeZeroIso.hom

/-- The exact reverse-simplicial-space map obtained by applying the
original discrete dagger embedding to `c†`. -/
def collapseReverse : walkingUnitarySpace.{0} ⟶ daggerSimplex 0 :=
  discreteDagger.map collapseDagger

/-- The original free dagger zero-simplex is terminal. -/
def freeZeroIsTerminal : IsTerminal (freeSimplex.{0} 0) :=
  DaggerSSet.pointIsTerminal.ofIso
    DaggerOriginalTaggedFreeZeroNativeWitness.pointFreeZeroIso

/-- The manuscript's selected vertex followed by the specified collapse
is the literal identity of the free dagger zero-simplex. -/
theorem unitaryVertex_collapse :
    unitaryVertex.{0} ≫ collapseDagger = 𝟙 (freeSimplex 0) :=
  freeZeroIsTerminal.hom_ext _ _

/-- The exact completeness map is split by the exact reverse-space
collapse. -/
theorem unitaryCompletenessMap_collapseReverse :
    unitaryCompletenessMap.{0} ≫ collapseReverse =
      𝟙 (daggerSimplex 0) := by
  change discreteDagger.map unitaryVertex ≫
      discreteDagger.map collapseDagger = 𝟙 _
  rw [← discreteDagger.map_comp, unitaryVertex_collapse,
    discreteDagger.map_id]

/-- The canonical walking collapse is surjective on the actual one-object
target. -/
private theorem walkingCollapse_surjective :
    Function.Surjective walkingCollapse.obj := by
  intro y
  refine ⟨walkingZero, ?_⟩
  cases y
  rfl

/-- Each Hom map of the walking collapse is an isomorphism of constant
one-point simplicial sets. -/
private theorem walkingCollapse_hom_isIso
    (x y : (DaggerUnitaryDiscrete.ordinaryEnrichment walkingIso.{0}).Obj) :
    IsIso (walkingCollapse.map x y) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro q
  rw [isIso_iff_bijective]
  haveI : Subsingleton
      (((DaggerUnitaryDiscrete.ordinaryEnrichment walkingIso.{0}).enriched.Hom
        x y).obj q) := by
    change Subsingleton (@Quiver.Hom walkingIso.{0} inferInstance x y)
    infer_instance
  haveI : Inhabited
      (((DaggerUnitaryDiscrete.ordinaryEnrichment walkingIso.{0}).enriched.Hom
        x y).obj q) := by
    change Inhabited (@Quiver.Hom walkingIso.{0} inferInstance x y)
    exact ⟨⟨⟨⟩⟩⟩
  haveI : Subsingleton
      (((DaggerDiscreteObjects.point.{0, 0}).enriched.Hom
        (walkingCollapse.obj x) (walkingCollapse.obj y)).obj q) := by
    change Subsingleton (ULift.{0} (PLift (PUnit.unit = PUnit.unit)))
    infer_instance
  constructor
  · intro a b _
    exact Subsingleton.elim a b
  · intro b
    exact ⟨default, Subsingleton.elim _ _⟩

/-- The exact walking collapse is locally geometric weak in the original
dagger Bergner class. -/
private theorem walkingCollapse_local :
    DaggerGlobalDK.LocalGeometricWeakEquivalence walkingCollapse := by
  intro x y
  change DaggerSSetGluing.GW (walkingCollapse.map x y)
  letI : IsIso (walkingCollapse.map x y) :=
    walkingCollapse_hom_isIso x y
  letI : WeakEquivalence (walkingCollapse.map x y) := inferInstance
  exact (DaggerSSetGluing.weakEquivalence_iff_GW _).1 inferInstance

/-- The canonical walking collapse is an original dagger DK weak
equivalence, with its object condition and all Hom maps verified. -/
theorem walkingCollapse_weak : WeakEquivalence walkingCollapse := by
  apply (weakEquivalence_iff walkingCollapse).2
  rw [DaggerActualRigidificationQuillen.target_weak]
  exact DaggerGlobalDK.daggerDK_of_surjective_local
    DaggerUnitaryInvariance.standardReplacement walkingCollapse
    walkingCollapse_surjective walkingCollapse_local

/-- Constant Hom simplicial sets make the walking unitary enrichment
fibrant in the original dagger Bergner model. -/
private theorem walkingEnrichment_fibrant :
    IsFibrant (DaggerUnitaryDiscrete.ordinaryEnrichment walkingIso.{0}) := by
  apply (DaggerGlobalFibrancy.standard_fibrant_iff_original _).2
  intro x y
  change SSet.KanComplex
    ((DaggerActualConstantSimplicialCategory.constant walkingIso.{0}).enriched.Hom x y)
  exact DaggerActualConstantSimplicialCategory.constant_locallyKan _ x y

/-- The chosen point category is fibrant because it is terminal in the
original dagger Bergner model. -/
private theorem pointEnrichment_fibrant :
    IsFibrant DaggerDiscreteObjects.point.{0, 0} := by
  exact (isFibrant_iff_of_isTerminal
    (𝟙 DaggerDiscreteObjects.point.{0, 0})
      DaggerDiscreteObjects.pointIsTerminal).2 (by infer_instance)

/-- The fixed Part I coherent nerve preserves this weak map between the
two explicitly fibrant enrichments. -/
private theorem coherentNerve_walkingCollapse_weak :
    WeakEquivalence (daggerCoherentNerve.map walkingCollapse) := by
  letI : IsFibrant
      (DaggerUnitaryDiscrete.ordinaryEnrichment walkingIso.{0}) :=
    walkingEnrichment_fibrant
  letI : IsFibrant DaggerDiscreteObjects.point.{0, 0} :=
    pointEnrichment_fibrant
  letI : WeakEquivalence walkingCollapse := walkingCollapse_weak
  letI : DaggerActualRigidificationQuillen.adjunction.{0}.IsQuillenAdjunction :=
    DaggerActualRigidificationQuillen.isQuillen
  letI : daggerCoherentNerve.{0}.PreservesTrivialFibrations :=
    Adjunction.IsQuillenAdjunction.preservesTrivialFibrations
      DaggerActualRigidificationQuillen.adjunction
  let b : FibrantBrownFactorization walkingCollapse :=
    Classical.choice inferInstance
  haveI : Fibration b.p := (fibration_iff _).mpr b.hp
  haveI : WeakEquivalence b.p := inferInstance
  haveI : WeakEquivalence b.r := inferInstance
  haveI : WeakEquivalence (daggerCoherentNerve.map b.p) := inferInstance
  haveI : WeakEquivalence (daggerCoherentNerve.map b.r) := inferInstance
  have hbr : daggerCoherentNerve.map b.i ≫
      daggerCoherentNerve.map b.r =
        𝟙 (daggerCoherentNerve.obj
          (DaggerUnitaryDiscrete.ordinaryEnrichment walkingIso.{0})) := by
    rw [← daggerCoherentNerve.map_comp, b.i_r,
      daggerCoherentNerve.map_id]
  have hi : WeakEquivalence (daggerCoherentNerve.map b.i) :=
    weakEquivalence_of_postcomp_of_fac hbr
  rw [← b.fac, daggerCoherentNerve.map_comp]
  infer_instance

/-- The specified `c†` is weak in the original dagger Joyal model. -/
theorem collapseDagger_weak : WeakEquivalence collapseDagger := by
  dsimp [collapseDagger]
  letI : WeakEquivalence (daggerCoherentNerve.map walkingCollapse) :=
    coherentNerve_walkingCollapse_weak
  infer_instance

/-- The manuscript's selected zero-vertex map is weak in the original
dagger Joyal model, by the exact retraction through `c†`. -/
theorem unitaryVertex_weak : WeakEquivalence unitaryVertex.{0} := by
  letI : WeakEquivalence collapseDagger := collapseDagger_weak
  exact weakEquivalence_of_postcomp_of_fac unitaryVertex_collapse

/-- The actual bar frame realization sends the specified interval collapse
to a weak equivalence in the original dagger Bergner model. -/
theorem frameRealization_bar_collapse_weak :
    weakEquivalences DaggerSimplicialCat.{0, 0}
      (JTFrameAdjunction.frameRealization.map
        (JTProjectiveBar.barOnDagger.map collapseDagger)) := by
  exact JTBarFunctorWeak.frameRealization_bar_map_weak
    collapseDagger ((weakEquivalence_iff collapseDagger).1 collapseDagger_weak)

/-- Every cofibrant arrow resolution of the **literal** unitary
completeness map has weak actual frame-realization image. -/
theorem frameRealization_completeness_resolution_weak
    (R : CofibrantArrowResolution unitaryCompletenessMap.{0}) :
    weakEquivalences DaggerSimplicialCat.{0, 0}
      (JTFrameAdjunction.frameRealization.map R.hom) := by
  have hf : DaggerJoyalWeakProperties.standardJoyalWeakEquivalences
      unitaryVertex.{0} := by
    rw [← DaggerActualRigidificationQuillen.source_weak]
    exact (weakEquivalence_iff unitaryVertex).1 unitaryVertex_weak
  exact JTCofibrantAugmentationWeak.frameRealization_resolution_weak
    unitaryVertex hf R

end

end DaggerModels.PartII.JTWalkingUnitaryWeak
