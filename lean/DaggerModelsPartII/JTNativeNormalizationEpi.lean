import OriginalFlagNormalizationJointImages
import OriginalFlagFlankedCodeEpi

/-!
# The original full necklace normalization is epic
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerChosenRigidificationNecklace NecklaceCode

namespace DaggerModels.PartII.JTNativeNormalizationEpi

open DaggerOriginalFlagFlankification

noncomputable section

universe u

private def endsFlag (T : NecklaceCode) : Flag.{u} T 1 where
  chain :=
    { toFun := Fin.cases {v : Vertices.{u} T | v.down ∈ T.joints} (fun _ ↦ Set.univ)
      monotone' := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all
        exact Set.subset_univ _ }
  joints _ h := h

private theorem endsFlag_flanked (T : NecklaceCode) : Flanked (endsFlag.{u} T) :=
  ⟨rfl, rfl⟩

/-- The degree-one flag used for the original normalization and its
literal image are both flanked. -/
theorem originalNormalization_exists_flanked {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)}
    (P : NecklacesOver X a b) :
    ∃ F : Flag.{u} P.code 1, Flanked F ∧
      Flanked (NecklaceCode.Flag.map (originalNormalization P).hom F) :=
  ⟨endsFlag P.code, endsFlag_flanked P.code,
    originalNormalizedFlag_flanked P _ (endsFlag_flanked P.code)⟩

/-- The actual normalization map lifts every simplex of its normalized
necklace. Apply the existing epimorphism theorem to its flanked flag. -/
theorem originalNormalization_epi {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)}
    (P : NecklacesOver X a b) : Epi (originalNormalization P).hom.map :=
  flanked_code_epi (endsFlag P.code) (originalNormalizedFlag P (endsFlag P.code))
    (originalNormalization P).hom rfl (endsFlag_flanked P.code)
    (originalNormalizedFlag_flanked P _ (endsFlag_flanked P.code))

end

end DaggerModels.PartII.JTNativeNormalizationEpi
