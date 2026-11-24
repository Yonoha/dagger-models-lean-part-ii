import DaggerModelsPartII.JTInjectiveOrderedFiberTransfer
import NativeKanRigHomWeakRecognition

/-! The actual injective comparison for chosenPsi has the ordered mapping
space and component hypotheses of the manuscript's recognition criterion. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra MorphismProperty
open DaggerModels
open DaggerOriginalSimplicialPiZeroWeakEquivalence
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTStrictificationInjectiveComparison

open SegalLocalizers JTStrictificationCoefficients
open JTProjectiveOrderedFiberComparison JTFirstRowWeakRecognition
open JTChosenPsiOrderedFiber JTChosenPsiVertices
open JTInjectiveFrameNerveTests JTPQOrderedFiberTransfer JTInjectiveOrderedFiberTransfer

noncomputable section

private abbrev S := ReverseDaggerSpace.{0}
private abbrev J := ReverseSimplexᵒᵖ

local instance : ModelCategory S := InjectiveKanDiagram.modelCategory J
local instance : ModelCategory DaggerSimplicialCat.{0, 0} :=
  DaggerActualRigidificationQuillen.modelG.{0}

/-- The selected original injective-local replacement of the frame nerve. -/
abbrev target (W : S) := (@frameNerveTest (rigidCoefficient (chosenT W))
  (rigidCoefficient_fibrant (chosenT W))).target

theorem target_local (W : S) : Localization.localObject localizingFamily (target W) :=
  (@frameNerveTest (rigidCoefficient (chosenT W)) (rigidCoefficient_fibrant (chosenT W))).localObject

/-- The actual lift of the specified composite to the injectively fibrant source. -/
def comparison (W : S) : (factor W).Z ⟶ target W := by
  letI := (target_local W).1
  exact extend (chosenComposite W)

theorem comparison_on_source (W : S) :
    (factor W).i ≫ comparison W = chosenComposite W := by
  letI := (target_local W).1
  exact extend_i (chosenComposite W)

private theorem rowMap_comp_zero {A B C : S} (f : A ⟶ B) (g : B ⟶ C) :
    rowMap (f ≫ g) ⦋0⦌ = rowMap f ⦋0⦌ ≫ rowMap g ⦋0⦌ := by
  apply NatTrans.ext
  funext n z
  rfl

private theorem composite_components_surjective (W : S) :
    Function.Surjective (SSet.mapπ₀ (rowMap (chosenComposite W) ⦋0⦌)) := by
  let C := rigidCoefficient (chosenT W)
  letI : IsFibrant C := rigidCoefficient_fibrant (chosenT W)
  let T := frameNerveTest C
  haveI : WeakEquivalence (rowMap (q C) ⦋0⦌) :=
    rowMap_weak_of_projective (q C) T.rowwiseWeak ⦋0⦌
  have hpsi : Function.Surjective ((rowMap (chosenPsi W) ⦋0⦌).app (op ⦋0⦌)) :=
    (chosenPsi_zero_bijective W).2
  have hπ := DaggerNativeKanRigHomWeakRecognition.mapπ₀_surjective_of_vertices
    (rowMap (chosenPsi W) ⦋0⦌) hpsi
  change Function.Surjective (SSet.mapπ₀ (rowMap (chosenPsi W ≫ q C) ⦋0⦌))
  rw [rowMap_comp_zero]
  intro z
  obtain ⟨y, hy⟩ := (bijective_mapPiZero (rowMap (q C) ⦋0⦌)).2 z
  obtain ⟨x, hx⟩ := hπ y
  exact ⟨x, by rw [SSet.mapπ₀_comp_apply, hx, hy]⟩

/-- The comparison is surjective on the components of its original zero row. -/
theorem comparison_components_surjective (W : S) :
    Function.Surjective (SSet.mapπ₀ (rowMap (comparison W) ⦋0⦌)) := by
  letI := (target_local W).1
  exact extend_components_surjective _ (composite_components_surjective W)

/-- Every actual strict mapping space of the comparison is weak under the
remaining original raw JT ordered-fiber weakness. -/
theorem comparison_strictFiber_weak (W : S) (hW : Localization.localObject localizingFamily W)
    (hraw : ∀ x y : (row (JTStrictificationMaps.Qproj.obj W) ⦋0⦌).obj (op ⦋0⦌),
      WeakEquivalence (JTRawOrdinaryAdjoint.rawChosenFiberMapAtP W x y))
    (x y : (row (factor W).Z ⦋0⦌).obj (op ⦋0⦌)) :
    WeakEquivalence (strictFiberMap (comparison W) x y) := by
  letI := hW.1
  letI := (target_local W).1
  exact extendedStrictFiber_weak (chosenComposite W)
    (fun a b ↦ compositeFiberMap_weak_of_raw W a b (hraw a b)) x y

/-- Local weakness of the actual injective comparison implies local weakness
of the original chosenPsi by its exact factorization and the specified q. -/
theorem chosenPsi_local_of_comparison_local (W : S)
    (h : Localization.localEquivalences localizingFamily (comparison W)) :
    Localization.localEquivalences localizingFamily (chosenPsi W) := by
  have hi : Localization.localEquivalences localizingFamily (factor W).i :=
    Localization.weakEquivalences_le_localEquivalences localizingFamily _
      (factor W).hi.2
  have hg : Localization.localEquivalences localizingFamily (chosenComposite W) := by
    rw [← comparison_on_source]
    exact (Localization.localEquivalences localizingFamily).comp_mem _ _ hi h
  let C := rigidCoefficient (chosenT W)
  letI : IsFibrant C := rigidCoefficient_fibrant (chosenT W)
  have hq : Localization.localEquivalences localizingFamily (q C) := by
    apply Localization.weakEquivalences_le_localEquivalences localizingFamily
    change (InjectiveKanDiagram.modelCategory J).categoryWithWeakEquivalences.weakEquivalences (q C)
    rw [← ProjectiveInjectiveComparison.weakEquivalences_eq J]
    exact (frameNerveTest C).rowwiseWeak
  exact (Localization.localEquivalences localizingFamily).of_postcomp (chosenPsi W) (q C) hq hg

end

end DaggerModels.PartII.JTStrictificationInjectiveComparison
