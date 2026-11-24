import DaggerModelsPartII.JTEndpointFrames
import DaggerModelsPartII.JTEndpointArrowReplacement
import DaggerModelsPartII.JTEndpointAugmentations
import DaggerModelsPartII.ArrowReedyCornerInterchange
import DaggerModelsPartII.ReedyCoefficientChange
import DaggerModelsPartII.StrictFrameMappingFibration
import Mathlib.CategoryTheory.Limits.Preserves.Opposites

/-!
# The resolved Xi endpoint mapping fibration

The actual zero-fixed qX replacement has projective Arrow relative matching
maps and a relative endpoint-face cofibration. Its two coefficient diagrams
are Reedy cofibrant, and their structure maps are weak by the original
augmentation. Thus its literal strict endpoint Hom map is a Kan fibration.
This statement concerns qX, not the raw Xi endpoint arrow.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTXiEndpointMappingFibration

open JTRelativeReedyFrame JTEndpointArrowReplacement
open JTEndpointAugmentations JTEndpointCobaseAugmentations
open ArrowReedyCornerInterchange

noncomputable section

private local instance : HasLimits Coefficient := daggerSimplicialCatHasLimits
private local instance : HasColimits Coefficient := daggerSimplicialCatHasColimits
private local instance : ModelCategory Coefficient :=
  DaggerActualRigidificationQuillen.modelG.{0}
private local instance : ModelCategory Coefficientᵒᵖ := inferInstance
private local instance : ModelCategory (SimplexCategoryᵒᵖ ⥤ Coefficientᵒᵖ) :=
  simplicialReedyModelCategory Coefficientᵒᵖ

private def L : (Arrow Coefficient)ᵒᵖ ⥤ Coefficientᵒᵖ :=
  (Arrow.leftFunc (C := Coefficient)).op

private def R : (Arrow Coefficient)ᵒᵖ ⥤ Coefficientᵒᵖ :=
  (Arrow.rightFunc (C := Coefficient)).op

private local instance : PreservesLimitsOfSize.{0, 0} L := by
  letI : PreservesColimitsOfSize.{0, 0} (Arrow.leftFunc (C := Coefficient)) :=
    ⟨fun {_} _ ↦ inferInstance⟩
  exact preservesLimitsOfSize_op _

/-- The source of the actual qX arrow diagram, with coefficient variance
reversed for the native Reedy model. -/
def qXiSourceOp : SimplexCategoryᵒᵖ ⥤ Coefficientᵒᵖ := QXop ⋙ L

/-- The target of the same actual qX arrow diagram. -/
def qXiTargetOp : SimplexCategoryᵒᵖ ⥤ Coefficientᵒᵖ := QXop ⋙ R

/-- Projective Arrow matching gives Reedy cofibrancy of qX's source. -/
theorem qXiSource_fibrant : IsFibrant qXiSourceOp := by
  let t := Functor.whiskerRight (secondRight ≫ firstRight) L
  have ht : IsTerminal
      ((⊤_ (SimplexCategoryᵒᵖ ⥤ (Arrow Coefficient)ᵒᵖ)) ⋙ L) :=
    terminalIsTerminal.isTerminalObj
      ((Functor.whiskeringRight SimplexCategoryᵒᵖ
        (Arrow Coefficient)ᵒᵖ Coefficientᵒᵖ).obj L) _
  apply (isFibrant_iff_of_isTerminal t ht).mpr
  apply (fibration_iff t).mpr
  intro n
  apply (ReedyCoefficientChange.relativeMatchingMap_property_iff
    (fibrations Coefficientᵒᵖ) L n (secondRight ≫ firstRight)).mp
  rw [fibrations_op]
  exact (QX_terminal_relativeMatching n).1

/-- The relative qX endpoint-face cofibration gives Reedy cofibrancy of
its target coefficient diagram. -/
theorem qXiTarget_fibrant : IsFibrant qXiTargetOp := by
  letI : IsFibrant (sourceOpp QXop) := qXiSource_fibrant
  have hf : Fibration (structureOpp QXop) := by
    apply (fibration_iff _).mpr
    intro n
    rw [fibrations_op]
    exact ArrowReedyCornerInterchange.Actual.QX_relativeCofibration n
  exact isFibrant_of_fibration (structureOpp QXop)

/-- Every structure map of the qX source is original weak, by the actual
source augmentation to the constant ordered boundary. -/
theorem qXiSource_maps_weak
    {s t : SimplexCategoryᵒᵖ} (θ : s ⟶ t) :
    weakEquivalences Coefficientᵒᵖ (qXiSourceOp.map θ) := by
  rw [weakEquivalences_op]
  let P := weakEquivalences Coefficient
  have hs : P ((sourceAug QXaugmentation).app s.unop) := by
    have hs : ⦋s.unop.len⦌ = s.unop := SimplexCategory.ext _ _ rfl
    rw [← hs]
    exact (QXaugmentation_weak s.unop.len).1
  have ht : P ((sourceAug QXaugmentation).app t.unop) := by
    have ht : ⦋t.unop.len⦌ = t.unop := SimplexCategory.ext _ _ rfl
    rw [← ht]
    exact (QXaugmentation_weak t.unop.len).1
  have h := (sourceAug QXaugmentation).naturality θ.unop
  change (qXiSourceOp.map θ).unop ≫
      (sourceAug QXaugmentation).app s.unop =
        (sourceAug QXaugmentation).app t.unop ≫ 𝟙 _ at h
  rw [Category.comp_id] at h
  exact P.of_postcomp _ _ hs (h.symm ▸ ht)

/-- Every structure map of the qX target is original weak, by its actual
augmentation to the original rigidified interval. -/
theorem qXiTarget_maps_weak
    {s t : SimplexCategoryᵒᵖ} (θ : s ⟶ t) :
    weakEquivalences Coefficientᵒᵖ (qXiTargetOp.map θ) := by
  rw [weakEquivalences_op]
  let P := weakEquivalences Coefficient
  have hs : P ((targetAug QXaugmentation).app s.unop) := by
    have hs : ⦋s.unop.len⦌ = s.unop := SimplexCategory.ext _ _ rfl
    rw [← hs]
    exact (QXaugmentation_weak s.unop.len).2
  have ht : P ((targetAug QXaugmentation).app t.unop) := by
    have ht : ⦋t.unop.len⦌ = t.unop := SimplexCategory.ext _ _ rfl
    rw [← ht]
    exact (QXaugmentation_weak t.unop.len).2
  have h := (targetAug QXaugmentation).naturality θ.unop
  change (qXiTargetOp.map θ).unop ≫
      (targetAug QXaugmentation).app s.unop =
        (targetAug QXaugmentation).app t.unop ≫ 𝟙 _ at h
  rw [Category.comp_id] at h
  exact P.of_postcomp _ _ hs (h.symm ▸ ht)

/-- The actual resolved qX endpoint Hom arrow is a Kan fibration for every
original fibrant dagger simplicial category. -/
theorem qXi_mapping_fibration (C : Coefficient) [IsFibrant C] :
    Fibration ((StrictFrameMappingWeak.strictMapping C).map
      (structureOpp QXop)) := by
  letI : IsFibrant qXiSourceOp := qXiSource_fibrant
  letI : IsFibrant qXiTargetOp := qXiTarget_fibrant
  exact StrictFrameMappingFibration.strictMapping_map_fibration C
    (fun θ ↦ qXiTarget_maps_weak θ)
    (fun θ ↦ qXiSource_maps_weak θ)
    (structureOpp QXop)
    (fun n ↦ by
      rw [fibrations_op]
      exact ArrowReedyCornerInterchange.Actual.QX_relativeCofibration n)

end

end DaggerModels.PartII.JTXiEndpointMappingFibration
