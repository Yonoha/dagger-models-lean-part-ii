import DaggerModelsPartII.ConstantVertexCofibrations
import DaggerModelsPartII.SmithCofibrantSourceGenerators
import Mathlib.CategoryTheory.LiftingProperties.Adjunction
import TopCatModelCategory.QuillenAdjunction

/-!
# The constant-vertex Quillen criterion

Weak preservation on cofibrant objects suffices for the literal constant-vertex
adjunction to be Quillen. The lifting argument uses the cofibrant-source Smith
generators of the original dagger Joyal model.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty DaggerModels

namespace DaggerModels.PartII.ConstantVertexAdjunction

open SegalLocalizers SmithCofibrantSourceGenerators

noncomputable section

private local instance : HasLimits DaggerSSet.{0} := daggerSSetHasLimits
private local instance : HasColimits DaggerSSet.{0} := daggerSSetHasColimits
private local instance : ModelCategory DaggerSSet.{0} :=
  DaggerOriginalJoyalModel.standardModelCategory.{0}
private local instance : ModelCategory ReverseDaggerSpace.{0} := injectiveSegalModel

/-- If constant vertex takes weak equivalences between cofibrant objects to
Segal-local weak equivalences, its adjunction with vertex evaluation is Quillen
for the original model structures. -/
theorem isQuillenAdjunction_of_cofibrant_weak
    (hδ : ∀ ⦃A B : DaggerSSet.{0}⦄ (i : A ⟶ B), IsCofibrant A → IsCofibrant B →
      weakEquivalences DaggerSSet.{0} i →
        weakEquivalences ReverseDaggerSpace.{0} (delta.map i)) :
    adjunction.IsQuillenAdjunction := by
  letI : delta.PreservesCofibrations := delta.preservesCofibrations_iff.mpr
    (by
      intro A B f hf
      exact delta_map_cofibration f hf)
  letI : vertex.PreservesFibrations := vertex.preservesFibrations_iff.mpr (by
    intro X Y p hp
    change fibrations DaggerSSet.{0} (vertex.map p)
    rw [← trivialCofibrations_rlp DaggerSSet.{0}, ← Jcof_rlp_llp, rlp_llp_rlp]
    intro A B i hi
    have hj : trivialCofibrations DaggerSSet.{0} i := by
      rw [← Jcof_rlp_llp]
      exact Jcof.le_llp_rlp i hi
    have hi' : trivialCofibrations ReverseDaggerSpace.{0} (delta.map i) :=
      ⟨delta_map_cofibration i hj.1,
        hδ i (Jcof_source_cofibrant hi) (Jcof_target_cofibrant hi) hj.2⟩
    have hl : HasLiftingProperty (delta.map i) p := by
      rw [← trivialCofibrations_rlp ReverseDaggerSpace.{0}] at hp
      exact hp _ hi'
    exact (adjunction.hasLiftingProperty_iff i p).mp hl)
  exact ⟨⟩

end

end DaggerModels.PartII.ConstantVertexAdjunction
