import DaggerModelsPartII.SmithCofibrantSourceSolution
import OriginalActualDaggerModelConstruction

/-!
# An alternate small trivial-cofibration family with cofibrant sources

The family uses the cofibrant-source Smith solution set. It defines a new
`Jcof`; the existing `generatedJ` and original model remain unchanged.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty DaggerModels

namespace DaggerModels.PartII.SmithCofibrantSourceGenerators

open SmithCofibrantSourceSolution

noncomputable section

private local instance : HasLimits DaggerSSet.{0} := daggerSSetHasLimits
private local instance : HasColimits DaggerSSet.{0} := daggerSSetHasColimits
private local instance : ModelCategory DaggerSSet.{0} :=
  DaggerOriginalJoyalModel.standardModelCategory.{0}
private local instance : IsLocallyPresentable.{0} DaggerSSet.{0} :=
  DaggerActualWeakAccessibility.NamespaceGate.actualDaggerSetLP
private local instance : MorphismProperty.IsSmall.{0}
    DaggerActualWeakAccessibility.originalID.{0} :=
  DaggerActualWeakAccessibility.originalID_small

private local instance cobaseStable :
    (DaggerActualWeakAccessibility.originalID.{0}.rlp.llp ⊓
      weakEquivalences DaggerSSet.{0}).IsStableUnderCobaseChange := by
  rw [DaggerOriginalJoyalModel.originalID_rlp_llp_eq_freeCofibrations]
  rw [← DaggerOriginalJoyalModel.standard_model_cof]
  change (trivialCofibrations DaggerSSet.{0}).IsStableUnderCobaseChange
  infer_instance

private local instance transfiniteStable :
    (DaggerActualWeakAccessibility.originalID.{0}.rlp.llp ⊓
      weakEquivalences DaggerSSet.{0}).IsStableUnderTransfiniteComposition := by
  rw [DaggerOriginalJoyalModel.originalID_rlp_llp_eq_freeCofibrations]
  rw [← DaggerOriginalJoyalModel.standard_model_cof]
  change (trivialCofibrations DaggerSSet.{0}).IsStableUnderTransfiniteComposition
  infer_instance

private theorem originalRLP_weak :
    DaggerActualWeakAccessibility.originalID.{0}.rlp ≤
      weakEquivalences DaggerSSet.{0} := by
  change DaggerActualWeakAccessibility.originalID.{0}.rlp ≤
    DaggerOriginalJoyalModel.standardModelCategory.{0}.categoryWithWeakEquivalences.weakEquivalences
  rw [DaggerOriginalJoyalModel.model_weak
    DaggerUnitaryInvariance.standardReplacement]
  exact DaggerOriginalDaggerBoundaryWeak.freeBoundary_rlp_le_joyalWeakEquivalences
    DaggerUnitaryInvariance.standardReplacement

/-- A new small Smith generating family, built from cofibrant-source selected arrows. -/
def Jcof : MorphismProperty DaggerSSet.{0} :=
  DaggerSmithSolutionSet.J standardRefinedSolution

instance Jcof_small : MorphismProperty.IsSmall.{0} Jcof :=
  DaggerSmithSolutionSet.instIsSmallJ standardRefinedSolution

/-- The new family generates the exact trivial cofibration class of the
original standard dagger Joyal model. -/
theorem Jcof_rlp_llp :
    Jcof.rlp.llp = trivialCofibrations DaggerSSet.{0} := by
  have h := DaggerSmithSolutionSet.trivial_left_eq
    standardRefinedSolution originalRLP_weak
  change Jcof.rlp.llp =
    DaggerActualWeakAccessibility.originalID.{0}.rlp.llp ⊓
      weakEquivalences DaggerSSet.{0} at h
  rw [h, DaggerOriginalJoyalModel.originalID_rlp_llp_eq_freeCofibrations]
  change DaggerSSet.freeCofibrations.{0} ⊓
    DaggerOriginalJoyalModel.standardModelCategory.{0}.categoryWithWeakEquivalences.weakEquivalences =
      DaggerOriginalJoyalModel.standardModelCategory.{0}.categoryWithCofibrations.cofibrations ⊓
        DaggerOriginalJoyalModel.standardModelCategory.{0}.categoryWithWeakEquivalences.weakEquivalences
  rw [DaggerOriginalJoyalModel.standard_model_cof]

/-- Every member of the *new* generating family has cofibrant domain. -/
theorem Jcof_source_cofibrant {A B : DaggerSSet.{0}} {f : A ⟶ B}
    (hf : Jcof f) : IsCofibrant A := by
  rw [Jcof, DaggerSmithSolutionSet.J.eq_1] at hf
  obtain ⟨z, hz⟩ := (ofHoms_iff _ f).mp hf
  let e := (DaggerSmithSolutionSet.indexEquiv
    DaggerActualWeakAccessibility.originalID.{0}
    (weakEquivalences DaggerSSet.{0}) standardRefinedSolution).symm z
  have hA : A = (standardRefinedSolution.arrow e.fst e.snd.fst).left :=
    congrArg (fun a : Arrow DaggerSSet.{0} ↦ a.left) hz
  rw [hA]
  exact standardRefinedSolution_source_cofibrant e.fst e.snd.fst

/-- The codomain is also cofibrant because a member of the Smith family is
an original cofibration and its source was just shown cofibrant. -/
theorem Jcof_target_cofibrant {A B : DaggerSSet.{0}} {f : A ⟶ B}
    (hf : Jcof f) : IsCofibrant B := by
  letI : IsCofibrant A := Jcof_source_cofibrant hf
  have hmem := DaggerSmithSolutionSet.J_le standardRefinedSolution
    originalRLP_weak f hf
  have hcof : cofibrations DaggerSSet.{0} f := by
    change DaggerOriginalJoyalModel.standardModelCategory.{0}.categoryWithCofibrations.cofibrations f
    rw [DaggerOriginalJoyalModel.standard_model_cof,
      ← DaggerOriginalJoyalModel.originalID_rlp_llp_eq_freeCofibrations]
    exact hmem.1
  letI : Cofibration f := (cofibration_iff _).mpr hcof
  exact isCofibrant_of_cofibration f

end

end DaggerModels.PartII.SmithCofibrantSourceGenerators
