import DaggerModelsPartII.MappingGeneratorDetection
import DaggerModelsPartII.ResolutionLocalEvaluation

/-! The exact local objects of the Part II collapse family. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite Simplicial
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII

noncomputable local instance localCharacterizationLimits : HasLimits DaggerSSet.{u} := daggerSSetHasLimits
noncomputable local instance localCharacterizationColimits : HasColimits DaggerSSet.{u} := daggerSSetHasColimits
noncomputable local instance localCharacterizationCoefficientModel : ModelCategory DaggerSSet.{u} :=
  DaggerOriginalJoyalModel.standardModelCategory
noncomputable local instance localCharacterizationReedyModel : ModelCategory ResolutionDiagram.{u} :=
  resolutionReedyModelCategory

/-- The actual free dagger boundaries and simplices detect weak equivalences between
fibrant dagger simplicial sets via their derived mapping simplicial sets. -/
theorem weak_of_resolutionTestObjects {X Y : DaggerSSet.{u}} [IsFibrant X] [IsFibrant Y]
    (f : X ⟶ Y)
    (h : ∀ (n : ℕ) (simplex : Bool), weakEquivalences SSet.{u}
      ((cosimplicialResolution (resolutionTestObject.{u} n simplex)).mappingSSet.map f)) :
    weakEquivalences DaggerSSet.{u} f := by
  letI : HasLimitsOfSize.{0, u} DaggerSSet.{u} := hasLimitsOfSizeShrink.{0, u} _
  let I : MorphismProperty DaggerSSet.{u} := DaggerActualWeakAccessibility.originalID.{u}
  have hI : I.rlp = trivialFibrations DaggerSSet.{u} :=
    (DaggerOriginalJoyalModel.model_trivialFibrations DaggerUnitaryInvariance.standardReplacement).symm
  have he : I = DaggerModels.freeBoundaryGenerators DaggerModels.freeDagger.{u} :=
    DaggerActualWeakAccessibility.originalID_eq
  have hcofI : I ≤ cofibrations DaggerSSet.{u} := by
    change I ≤ DaggerOriginalJoyalModel.standardModelCategory.categoryWithCofibrations.cofibrations
    rw [he, DaggerOriginalJoyalModel.standard_model_cof]
    exact DaggerModels.freeBoundaryGenerators_le _ DaggerModels.freeDaggerAdjunction
  refine TargetResolution.weak_of_generator_derivedMapping I hI hcofI f ?_ ?_
  · intro A B i hi
    rw [he] at hi
    obtain ⟨n⟩ := hi
    exact ⟨freeDagger_isCofibrant _, freeDagger_isCofibrant _⟩
  · intro A B i hi
    rw [he] at hi
    obtain ⟨n⟩ := hi
    exact ⟨h n false, h n true⟩

/-- Locality for the specified collapse family is precisely Reedy fibrancy and
homotopical constancy, expressed by the levelwise weak equivalence of the counit. -/
theorem resolutionLocalObject_iff_homotopicallyConstant (W : ResolutionDiagram.{u}) :
    resolutionLocalObject W ↔ IsFibrant W ∧ reedyWeakEquivalences (resolutionCounit W) := by
  constructor
  · intro h
    obtain ⟨hw, htest⟩ := (resolutionLocalObject_iff_coefficientMapping W).mp h
    letI := hw
    refine ⟨hw, ?_⟩
    intro k
    rw [← op_unop k, ← SimplexCategory.mk_len k.unop]
    cases k.unop.len with
    | zero =>
      change weakEquivalences DaggerSSet.{u} (W.map (simplexCollapse (op ⦋0⦌)).op)
      rw [simplexCollapse_zero_op, W.map_id]
      exact (weakEquivalences _).id_mem _
    | succ n =>
      letI := reedyFibrant_obj W (op ⦋0⦌)
      letI := reedyFibrant_obj W (op ⦋n + 1⦌)
      exact weak_of_resolutionTestObjects (W.map (simplexCollapse (op ⦋n + 1⦌)).op)
        (fun m simplex ↦ htest m simplex n)
  · rintro ⟨hw, h⟩
    letI := hw
    exact resolutionLocalObject_of_homotopicallyConstant W h

end DaggerModels.PartII
