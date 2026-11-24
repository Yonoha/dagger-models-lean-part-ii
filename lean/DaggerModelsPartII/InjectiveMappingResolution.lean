import DaggerModelsPartII.InjectiveStandardFrame

/-!
# The strict mapping space computes the homotopy function complex

A chosen cosimplicial resolution maps to the standard tensor frame over its
augmentation. Applying the levelwise Hom functor and the strict mapping-space
isomorphism gives a weak equivalence for every injectively fibrant target.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.InjectiveKanDiagram

noncomputable section

variable (C : Type u) [Category.{u} C] [hgen : Fact (GeneratorsAreAllMonos C)]

local instance resolutionInjectiveModel : ModelCategory (C ⥤ SSet.{u}) :=
  modelOfGeneratorDensity C hgen.out

local instance resolutionFrameModel : ModelCategory
    (SimplexCategoryᵒᵖ ⥤ (C ⥤ SSet.{u})ᵒᵖ) :=
  simplicialReedyModelCategory (C ⥤ SSet.{u})ᵒᵖ

private def standardFrameSquare (A : C ⥤ SSet.{u}) :=
  CommSq (standardAugmentation C A) (cosimplicialResolution A).augmentationOp
    (terminal.from (standardFrame C A))
    (terminal.from (cosimplicialResolution A).oppositeDiagram)

private def standardFrameSquare_comm (A : C ⥤ SSet.{u}) : standardFrameSquare C A :=
  ⟨terminal.hom_ext _ _⟩

private instance standardFrameSquare_lifting (A : C ⥤ SSet.{u}) :
    HasLiftingProperty (cosimplicialResolution A).augmentationOp
      (terminal.from (standardFrame C A)) := by
  letI := standardFrame_reedyFibrant C A
  exact hasLiftingProperty_of_wfs _ _ (cosimplicialResolution A).augmentationOp_mem
    (mem_fibrations _)

/-- A comparison from the chosen resolution to the standard tensor frame. -/
def chosenResolutionToStandardFrame (A : C ⥤ SSet.{u}) :
    (cosimplicialResolution A).oppositeDiagram ⟶ standardFrame C A :=
  (standardFrameSquare_comm C A).lift

/-- The comparison commutes with the two augmentations. -/
theorem chosenResolutionToStandardFrame_fac (A : C ⥤ SSet.{u}) :
    (cosimplicialResolution A).augmentationOp ≫ chosenResolutionToStandardFrame C A =
      standardAugmentation C A :=
  (standardFrameSquare_comm C A).fac_left

/-- The comparison is a Reedy weak equivalence. -/
theorem chosenResolutionToStandardFrame_weak (A : C ⥤ SSet.{u}) :
    HomotopicalAlgebra.weakEquivalences _ (chosenResolutionToStandardFrame C A) := by
  apply (HomotopicalAlgebra.weakEquivalences _).of_precomp _ _
    (cosimplicialResolution A).augmentationOp_mem.2
  rw [chosenResolutionToStandardFrame_fac]
  exact standardAugmentation_weak C A

/-- The map from a chosen homotopy function complex to the strict mapping space. -/
def chosenMappingToStrict (A W : C ⥤ SSet.{u}) :
    (cosimplicialResolution A).mappingSSet.obj W ⟶ diagramMappingSpace A W :=
  (CosimplicialResolution.mappingFromOppositeDiagram W).map
      (chosenResolutionToStandardFrame C A) ≫
    (standardFrameMappingIso C A W).hom

/-- For an injectively fibrant target, the comparison is a Kan weak equivalence. -/
theorem chosenMappingToStrict_weak (A W : C ⥤ SSet.{u}) [IsFibrant W] :
    HomotopicalAlgebra.weakEquivalences SSet.{u} (chosenMappingToStrict C A W) := by
  let R := cosimplicialResolution A
  letI := R.fibrantOp
  letI := standardFrame_reedyFibrant C A
  let F := CosimplicialResolution.mappingFromOppositeDiagram W
  have h := map_weak_of_trivialFibration F
    (fun p hp ↦ (CosimplicialResolution.mappingFromOppositeDiagram_map_trivialFibration
      W p hp).2) (chosenResolutionToStandardFrame C A)
    (chosenResolutionToStandardFrame_weak C A)
  exact (HomotopicalAlgebra.weakEquivalences SSet.{u}).comp_mem _ _ h
    ((HomotopicalAlgebra.weakEquivalences SSet.{u}).of_isIso _)

end

end DaggerModels.PartII.InjectiveKanDiagram
