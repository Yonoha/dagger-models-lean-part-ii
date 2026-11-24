import DaggerModelsPartII.JTTargetIntervalGluing
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! Glue complete time-parameterized maps along the actual inverse image of a target joint. -/

set_option autoImplicit false

open CategoryTheory Limits Simplicial MonoidalCategory
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTFullPrismTargetCut

open JTTargetIntervalGluing JTTargetJointMarks

noncomputable section

private instance tensorRight_preservesColimits (K : SSet.{0}) :
    PreservesColimitsOfSize.{1, 1} (tensorRight K) := by
  letI : BraidedCategory SSet.{0} := .ofCartesianMonoidalCategory
  letI : PreservesColimitsOfSize.{1, 1} (tensorLeft K) := inferInstance
  exact preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight K)

variable {T U : NecklaceCode} (f : T ⟶ U) (j : Joint U) (K : SSet.{0})

/-- The complete parameterized source is the pushout of both actual inverse-image intervals. -/
theorem isPushout :
    IsPushout (middleLeft f j ▷ K) (middleRight f j ▷ K)
      (leftInclusion f j ▷ K) (rightInclusion f j ▷ K) :=
  (JTTargetIntervalGluing.isPushout f j).map (tensorRight K)

variable (Z : SSet.{0})

/-- Two whole parameter-dependent maps agreeing on the entire inverse image
of the joint. -/
abbrev Pair :=
  {p : (((Arrow.mk (leftInclusion f j)).left ⊗ K) ⟶ Z) ×
    (((Arrow.mk (rightInclusion f j)).left ⊗ K) ⟶ Z) //
      (middleLeft f j ▷ K) ≫ p.1 = (middleRight f j ▷ K) ≫ p.2}

/-- Exact restriction and gluing of complete prism maps, including all their time simplices. -/
def restrictEquiv : (T.toSSet ⊗ K ⟶ Z) ≃ Pair f j K Z where
  toFun p := ⟨((leftInclusion f j ▷ K) ≫ p, (rightInclusion f j ▷ K) ≫ p), by
    rw [← Category.assoc, ← Category.assoc, (isPushout f j K).w]⟩
  invFun p := (isPushout f j K).desc p.val.1 p.val.2 p.property
  left_inv p := (isPushout f j K).hom_ext
    ((isPushout f j K).inl_desc _ _ _) ((isPushout f j K).inr_desc _ _ _)
  right_inv p := Subtype.ext (Prod.ext ((isPushout f j K).inl_desc _ _ _)
    ((isPushout f j K).inr_desc _ _ _))

section Naturality

open JTTargetIntervalPullback (sourceMap sourceMap_fac)

variable {T' : NecklaceCode} {f' : T' ⟶ U} (a : T ⟶ T') (ha : a ≫ f' = f)
variable {K' : SSet.{0}} (v : K ⟶ K')

private theorem tensorSquare {A B C D K₀ K₁ : SSet.{0}}
    (p : A ⟶ C) (q : B ⟶ D) (u : A ⟶ B) (v : C ⟶ D) (r : K₀ ⟶ K₁)
    (h : u ≫ q = p ≫ v) :
    (p ▷ K₀) ≫ (v ⊗ₘ r) = (u ⊗ₘ r) ≫ (q ▷ K₁) := by
  change (p ⊗ₘ 𝟙 K₀) ≫ (v ⊗ₘ r) = (u ⊗ₘ r) ≫ (q ⊗ₘ 𝟙 K₁)
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id, h]

/-- Restricting the whole product to the left interval commutes with the actual
native arrow and any time operator. -/
theorem left_map :
    (leftInclusion f j ▷ K) ≫ (a.map ⊗ₘ v) =
      (sourceMap f ⟨0, U.first_mem⟩ j (Fin.zero_le j.val) a ha ⊗ₘ v) ≫
        (leftInclusion f' j ▷ K') := by
  exact tensorSquare _ _ _ _ _ (sourceMap_fac _ _ _ _ a ha)

/-- Restricting the whole product to the right interval commutes with the actual
native arrow and any time operator. -/
theorem right_map :
    (rightInclusion f j ▷ K) ≫ (a.map ⊗ₘ v) =
      (sourceMap f j ⟨Fin.last U.len, U.last_mem⟩ (Fin.le_last j.val) a ha ⊗ₘ v) ≫
        (rightInclusion f' j ▷ K') := by
  exact tensorSquare _ _ _ _ _ (sourceMap_fac _ _ _ _ a ha)

end Naturality

end
end DaggerModels.PartII.JTFullPrismTargetCut
