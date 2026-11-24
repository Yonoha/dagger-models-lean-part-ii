import DaggerModelsPartII.InjectiveKanRecognition
import DaggerModelsPartII.DiagramTensorMappingAdjunction
import OrdinaryAnodyneTensor

/-! Kan mapping spaces for the injective classes, conditional on generator density. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.InjectiveKanDiagram

noncomputable section

variable (C : Type u) [Category.{u} C] [hgen : Fact (GeneratorsAreAllMonos C)]

local instance : ModelCategory (C ⥤ SSet.{u}) := modelOfGeneratorDensity C hgen.out

/-- Every diagram is cofibrant for the injective model. -/
theorem everyObject_isCofibrant (A : C ⥤ SSet.{u}) : IsCofibrant A := by
  apply (HomotopicalAlgebra.cofibration_iff _).mpr
  change (modelOfGeneratorDensity C hgen.out).categoryWithCofibrations.cofibrations _
  rw [(modelOfGeneratorDensity_exactClasses C hgen.out).1]
  change Mono (initial.to A)
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro c
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro n
  let E := (evaluation C SSet.{u}).obj c ⋙ SSet.evaluation.obj n
  exact (initialIsInitial.isInitialObj E).mono_from _

/-- Levelwise tensoring with a fixed diagram preserves trivial cofibrations
for the injective classes. -/
theorem diagramTensor_preservesTrivialCofibrations (A : C ⥤ SSet.{u}) :
    (diagramTensor A).PreservesTrivialCofibrations := by
  constructor
  intro K L j hj
  have ha : SSet.anodyneExtensions j :=
    (DaggerOrdinaryAnodyneTensor.anodyne_iff_trivialCofibration j).mpr hj
  have hpoint :
      (HomotopicalAlgebra.trivialCofibrations SSet.{u}).functorCategory C
        ((diagramTensor A).map j) := by
    intro c
    exact (DaggerOrdinaryAnodyneTensor.anodyne_iff_trivialCofibration _).mp
      (DaggerOrdinaryAnodyneTensor.whiskerLeft j ha (A.obj c))
  have ht : trivialCofibrations C ((diagramTensor A).map j) := by
    rw [trivialCofibrations_eq]
    exact hpoint
  change (modelOfGeneratorDensity C hgen.out).categoryWithCofibrations.cofibrations
      ((diagramTensor A).map j) ∧
    (modelOfGeneratorDensity C hgen.out).categoryWithWeakEquivalences.weakEquivalences
      ((diagramTensor A).map j)
  rw [(modelOfGeneratorDensity_exactClasses C hgen.out).1,
    (modelOfGeneratorDensity_exactClasses C hgen.out).2]
  exact ht

/-- Tensoring with any fixed diagram preserves injective cofibrations. -/
theorem diagramTensor_preservesCofibrations (A : C ⥤ SSet.{u}) :
    (diagramTensor A).PreservesCofibrations := by
  refine (diagramTensor A).preservesCofibrations_iff.mpr fun K L j hj ↦ ?_
  haveI : Mono j := (SSet.modelCategoryQuillen.cofibration_iff j).mp
    ((HomotopicalAlgebra.cofibration_iff j).mpr hj)
  have hm : Mono ((diagramTensor A).map j) := by
    apply (NatTrans.mono_iff_mono_app _).mpr
    intro c
    apply (NatTrans.mono_iff_mono_app _).mpr
    intro n
    apply (CategoryTheory.mono_iff_injective _).mpr
    intro a b h
    have hjn : Function.Injective (j.app n) :=
      (CategoryTheory.mono_iff_injective _).mp inferInstance
    change (a.1, j.app n a.2) = (b.1, j.app n b.2) at h
    exact Prod.ext (congrArg (fun z : (A.obj c).obj n × L.obj n ↦ z.1) h)
      (hjn (congrArg (fun z : (A.obj c).obj n × L.obj n ↦ z.2) h))
  change (modelOfGeneratorDensity C hgen.out).categoryWithCofibrations.cofibrations _
  rw [(modelOfGeneratorDensity_exactClasses C hgen.out).1]
  exact hm

/-- The mapping-space right adjoint preserves fibrations for these injective classes. -/
theorem diagramMappingTarget_preservesFibrations (A : C ⥤ SSet.{u}) :
    (diagramMappingTarget A).PreservesFibrations :=
  (diagramTensorMappingAdjunction A).preservesTrivialCofibrations_iff_preservesFibrations.mp
    (diagramTensor_preservesTrivialCofibrations C A)

/-- Tensor and mapping space form a Quillen adjunction for each fixed diagram. -/
theorem diagramTensorMapping_isQuillen (A : C ⥤ SSet.{u}) :
    (diagramTensorMappingAdjunction A).IsQuillenAdjunction := by
  letI := diagramTensor_preservesCofibrations C A
  letI := diagramMappingTarget_preservesFibrations C A
  exact ⟨⟩

/-- An injectively fibrant target has Kan mapping space out of every diagram. -/
theorem diagramMappingSpace_isFibrant (A W : C ⥤ SSet.{u}) [IsFibrant W] :
    IsFibrant (diagramMappingSpace A W) := by
  let R := diagramMappingTarget A
  letI : R.PreservesFibrations := diagramMappingTarget_preservesFibrations C A
  letI : PreservesLimitsOfSize.{0, 0} R :=
    (diagramTensorMappingAdjunction A).rightAdjoint_preservesLimits
  exact (isFibrant_iff_of_isTerminal (R.map (terminal.from W))
    (terminalIsTerminal.isTerminalObj R)).mpr inferInstance

end

end DaggerModels.PartII.InjectiveKanDiagram
