import ActualDaggerRigidificationQuillen
import DaggerModelsPartII.AccessibleTerminalReplacement

/-! Functorial fibrant replacement in the original dagger Bergner model. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty DaggerModels

namespace DaggerModels.PartII.JTFunctorialBergnerReplacement

noncomputable section

private abbrev B := DaggerSimplicialCat.{0, 0}

private local instance : ModelCategory B := DaggerActualRigidificationQuillen.modelG.{0}
private local instance : HasLimits B := daggerSimplicialCatHasLimits
private local instance : HasColimits B := daggerSimplicialCatHasColimits
private local instance : IsLocallyPresentable.{0} B := daggerSimplicialCatLocallyPresentable

private theorem generator_rlp : DaggerGlobalJLifting.J.{0}.rlp = fibrations B :=
  DaggerGlobalModel.standardCombinatorialData.fibrations

/-- Apply the existing terminal small-object construction to the original acyclic family. -/
def replacement : B ⥤ B := SmallObjectReplacement.replacement DaggerGlobalJLifting.J.{0}

/-- The original terminal replacement map, natural in the coefficient. -/
def unit : 𝟭 B ⟶ replacement := SmallObjectReplacement.unit DaggerGlobalJLifting.J.{0}

theorem isFibrant (X : B) : IsFibrant (replacement.obj X) := by
  rw [isFibrant_iff, fibration_iff, ← generator_rlp]
  exact SmallObjectReplacement.terminal_mem_rlp DaggerGlobalJLifting.J.{0} X

theorem unit_weak (X : B) : weakEquivalences B (unit.app X) := by
  have h := SmallObjectReplacement.unit_mem_llp DaggerGlobalJLifting.J.{0} X
  rw [generator_rlp, llp_eq_of_wfs (trivialCofibrations B) (fibrations B)] at h
  exact h.2

end

end DaggerModels.PartII.JTFunctorialBergnerReplacement
