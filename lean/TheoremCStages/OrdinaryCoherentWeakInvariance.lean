import OrdinaryCoherentArrowNaturality
import DaggerModelsPartII.CosimplicialMappingInvariance
import OriginalSimplicialPiZeroWeakEquivalence
import NativeSubcomplexWeakRestriction

/-!
# Coherent-arrow invariance under actual weak fibrant diagram maps

The existing injective tensor-mapping Quillen adjunction and Brown lemma give
weakness on whole walking mapping spaces between fibrant diagrams. Naturality
and bijectivity on components then identify the exact preimage of the coherent
component image. Native subcomplex pullbacks and right properness give weakness
of the same restricted arrow map. No Segal or completeness assumption is used.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryCoherentWeakInvariance

open OrdinaryCSSLocalization (Space walkingSpace)
open OrdinaryCoherentArrowNaturality
open OrdinarySegalWalkingEvaluation (edgeEvaluation)
open OrdinarySegalCoherentArrowImage (coherentArrowSubcomplex)
open OrdinarySegalComponentImage (imageComponents)

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

/-- The existing Brown argument for strict mapping spaces, at the ordinary index. -/
theorem mapping_weak (A : Space) {W Z : Space} [IsFibrant W] [IsFibrant Z]
    (f : W ⟶ Z) [WeakEquivalence f] :
    WeakEquivalence ((diagramMappingTarget A).map f) := by
  let adj := diagramTensorMappingAdjunction A
  letI : adj.IsQuillenAdjunction :=
    InjectiveKanDiagram.model_tensorMapping_isQuillen SimplexCategoryᵒᵖ A
  letI : (diagramMappingTarget A).PreservesTrivialFibrations :=
    Adjunction.IsQuillenAdjunction.preservesTrivialFibrations adj
  apply (weakEquivalence_iff _).mpr
  apply map_weak_of_trivialFibration (diagramMappingTarget A) _ f (mem_weakEquivalences _)
  intro X Y q hq
  haveI : Fibration q := (mem_trivialFibrations_iff q).mp hq |>.1
  haveI : WeakEquivalence q := (mem_trivialFibrations_iff q).mp hq |>.2
  exact mem_weakEquivalences _

/-- A weak injective diagram map has the original weak arrow-row component. -/
theorem row_weak {W Z : Space} (f : W ⟶ Z) [WeakEquivalence f]
    (q : SimplexCategoryᵒᵖ) : WeakEquivalence (f.app q) := by
  have h := mem_weakEquivalences f
  rw [InjectiveKanDiagram.model_weakEquivalences] at h
  exact (weakEquivalence_iff _).mpr (h q)

/-- For a weak map of fibrant diagrams, the source coherent components are
exactly the preimage of the target coherent components under the same row map. -/
theorem coherent_components_preimage {W Z : Space} [IsFibrant W] [IsFibrant Z]
    (f : W ⟶ Z) [WeakEquivalence f] (c : (W.obj (op ⦋1⦌)).π₀) :
    c ∈ imageComponents (edgeEvaluation W) ↔
      SSet.mapπ₀ (f.app (op ⦋1⦌)) c ∈ imageComponents (edgeEvaluation Z) := by
  haveI : WeakEquivalence (walkingMap f) := mapping_weak walkingSpace f
  haveI : WeakEquivalence (f.app (op ⦋1⦌)) := row_weak f _
  have hw := DaggerOriginalSimplicialPiZeroWeakEquivalence.bijective_mapPiZero (walkingMap f)
  have hf := DaggerOriginalSimplicialPiZeroWeakEquivalence.bijective_mapPiZero
    (f.app (op ⦋1⦌))
  have hs := congrArg SSet.mapπ₀ (edgeEvaluation_post f)
  constructor
  · rintro ⟨d, rfl⟩
    refine ⟨SSet.mapπ₀ (walkingMap f) d, ?_⟩
    simpa only [SSet.mapπ₀_comp_apply] using congrFun hs d
  · rintro ⟨d, hd⟩
    obtain ⟨e, he⟩ := hw.surjective d
    refine ⟨e, hf.injective ?_⟩
    have h := congrFun hs e
    simpa only [SSet.mapπ₀_comp_apply, he, hd] using h.symm

/-- The actual arrow simplices reflect coherent membership in every degree. -/
theorem coherent_membership_iff {W Z : Space} [IsFibrant W] [IsFibrant Z]
    (f : W ⟶ Z) [WeakEquivalence f] (q : SimplexCategoryᵒᵖ)
    (e : (W.obj (op ⦋1⦌)).obj q) :
    e ∈ (coherentArrowSubcomplex W).obj q ↔
      (f.app (op ⦋1⦌)).app q e ∈ (coherentArrowSubcomplex Z).obj q := by
  change e ∈ (OrdinarySegalComponentImage.componentImage (edgeEvaluation W)).obj q ↔
    (f.app (op ⦋1⦌)).app q e ∈
      (OrdinarySegalComponentImage.componentImage (edgeEvaluation Z)).obj q
  simp only [OrdinarySegalComponentImage.componentImage,
    OrdinarySegalComponentSubcomplex.mem_selected_iff,
    OrdinarySegalComponentSubcomplex.simplexComponent_map]
  exact coherent_components_preimage f _

/-- The same restricted coherent-arrow action of a weak fibrant map is weak. -/
theorem coherentArrowMap_weak {W Z : Space} [IsFibrant W] [IsFibrant Z]
    (f : W ⟶ Z) [WeakEquivalence f] :
    WeakEquivalence (coherentArrowMap f) := by
  haveI : WeakEquivalence (f.app (op ⦋1⦌)) := row_weak f _
  haveI : Fibration (coherentArrowSubcomplex Z).ι :=
    OrdinarySegalCoherentArrowImage.coherentArrow_inclusion_fibration Z
  exact DaggerNativeSubcomplexWeakRestriction.weakEquivalence
    (f.app (op ⦋1⦌)) (coherentArrowSubcomplex W) (coherentArrowSubcomplex Z)
    (coherentArrowMap f) (coherentArrowMap_inclusion f)
    (coherent_membership_iff f)

#print axioms mapping_weak
#print axioms coherent_components_preimage
#print axioms coherent_membership_iff
#print axioms coherentArrowMap_weak

end

end DaggerModels.PartII.OrdinaryCoherentWeakInvariance
