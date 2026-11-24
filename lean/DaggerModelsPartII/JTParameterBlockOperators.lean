import DaggerModelsPartII.JTParameterBlocks
import OriginalOrdinalJoinLeft

/-! Functorial separated parameter blocks, with the exact endpoint hypotheses
needed by the clamping maps in binary label gluing.

The operators are Mathlib's augmented ordinal-sum tensor, as already used
by `DaggerOriginalOrdinalJoinLeft`. The endpoint equations concern the
original `JTParameterBlocks.leftRet` and `rightRet`.
-/

set_option autoImplicit false

open CategoryTheory Simplicial MonoidalCategory

namespace DaggerModels.PartII.JTParameterBlockOperators

open JTParameterBlocks
open AugmentedSimplexCategory (tensorHomOf inl' inr')

variable {k l k' l' k'' l'' : SimplexCategory}

/-- The literal ordinal sum of two operators on the existing blocks. -/
abbrev map (a : k ⟶ k') (b : l ⟶ l') : common k l ⟶ common k' l' :=
  tensorHomOf a b

theorem map_id (k l : SimplexCategory) : map (𝟙 k) (𝟙 l) = 𝟙 (common k l) :=
  AugmentedSimplexCategory.tensor_id (.of k) (.of l)

theorem map_comp (a : k ⟶ k') (a' : k' ⟶ k'') (b : l ⟶ l') (b' : l' ⟶ l'') :
    map a b ≫ map a' b' = map (a ≫ a') (b ≫ b') :=
  AugmentedSimplexCategory.tensorHom_comp_tensorHom
    (show WithInitial.of k ⟶ WithInitial.of k' from a)
    (show WithInitial.of l ⟶ WithInitial.of l' from b)
    (show WithInitial.of k' ⟶ WithInitial.of k'' from a')
    (show WithInitial.of l' ⟶ WithInitial.of l'' from b')

private theorem leftIn_eq (k l : SimplexCategory) : leftIn k l = inl' k l := by
  ext i : 3
  apply Fin.ext
  exact (congrArg Fin.val (AugmentedSimplexCategory.inl'_eval k l i)).symm

private theorem rightIn_eq (k l : SimplexCategory) : rightIn k l = inr' k l := by
  ext i : 3
  apply Fin.ext
  exact (congrArg Fin.val (AugmentedSimplexCategory.inr'_eval k l i)).symm

@[reassoc] theorem leftIn_map (a : k ⟶ k') (b : l ⟶ l') :
    leftIn k l ≫ map a b = a ≫ leftIn k' l' := by
  rw [leftIn_eq, leftIn_eq]
  exact AugmentedSimplexCategory.inl_comp_tensorHom
    (show WithInitial.of k ⟶ WithInitial.of k' from a)
    (show WithInitial.of l ⟶ WithInitial.of l' from b)

@[reassoc] theorem rightIn_map (a : k ⟶ k') (b : l ⟶ l') :
    rightIn k l ≫ map a b = b ≫ rightIn k' l' := by
  rw [rightIn_eq, rightIn_eq]
  exact AugmentedSimplexCategory.inr_comp_tensorHom
    (show WithInitial.of k ⟶ WithInitial.of k' from a)
    (show WithInitial.of l ⟶ WithInitial.of l' from b)

/-- The original two block inclusions detect equality of whole ordinal maps. -/
theorem hom_ext {n : SimplexCategory} {f g : common k l ⟶ n}
    (hl : leftIn k l ≫ f = leftIn k l ≫ g)
    (hr : rightIn k l ≫ f = rightIn k l ≫ g) : f = g := by
  rw [leftIn_eq] at hl
  rw [rightIn_eq] at hr
  exact AugmentedSimplexCategory.tensorObj_hom_ext
    (x := .of k) (y := .of l) (z := .of n) f g hl hr

theorem rightIn_leftRet (k l : SimplexCategory) :
    rightIn k l ≫ leftRet k l = SimplexCategory.const l k (Fin.last k.len) := by
  ext i : 3
  apply Fin.ext
  change min (k.len + 1 + i.val) k.len = k.len
  omega

theorem leftIn_rightRet (k l : SimplexCategory) :
    leftIn k l ≫ rightRet k l = SimplexCategory.const k l 0 := by
  ext i : 3
  apply Fin.ext
  change i.val - (k.len + 1) = 0
  exact Nat.sub_eq_zero_of_le (Nat.le_of_lt i.isLt)

theorem leftIn_zero (k l : SimplexCategory) :
    (leftIn k l).toOrderHom 0 = 0 := rfl

theorem rightIn_last (k l : SimplexCategory) :
    (rightIn k l).toOrderHom (Fin.last l.len) = Fin.last (common k l).len := by
  apply Fin.ext
  change k.len + 1 + l.len = k.len + l.len + 1
  omega

/-- The left clamp commutes with a block operator whose left map fixes its last vertex. -/
theorem leftRet_map (a : k ⟶ k') (b : l ⟶ l')
    (ha : a.toOrderHom (Fin.last k.len) = Fin.last k'.len) :
    leftRet k l ≫ a = map a b ≫ leftRet k' l' := by
  apply hom_ext
  · rw [← Category.assoc, left_split, Category.id_comp, leftIn_map_assoc,
      left_split, Category.comp_id]
  · rw [← Category.assoc, rightIn_leftRet, SimplexCategory.const_comp, ha,
      rightIn_map_assoc, rightIn_leftRet]
    rfl

/-- The right clamp commutes with a block operator whose right map fixes its first vertex. -/
theorem rightRet_map (a : k ⟶ k') (b : l ⟶ l')
    (hb : b.toOrderHom 0 = 0) :
    rightRet k l ≫ b = map a b ≫ rightRet k' l' := by
  apply hom_ext
  · rw [← Category.assoc, leftIn_rightRet, SimplexCategory.const_comp, hb,
      leftIn_map_assoc, leftIn_rightRet]
    rfl
  · rw [← Category.assoc, right_split, Category.id_comp, rightIn_map_assoc,
      right_split, Category.comp_id]

theorem map_first (a : k ⟶ k') (b : l ⟶ l') (ha : a.toOrderHom 0 = 0) :
    (map a b).toOrderHom 0 = 0 := by
  have h := SimplexCategory.congr_toOrderHom_apply (leftIn_map a b) (0 : Fin (k.len + 1))
  change (map a b).toOrderHom ((leftIn k l).toOrderHom 0) =
    (leftIn k' l').toOrderHom (a.toOrderHom 0) at h
  rw [ha, leftIn_zero, leftIn_zero] at h
  exact h

theorem map_last (a : k ⟶ k') (b : l ⟶ l')
    (hb : b.toOrderHom (Fin.last l.len) = Fin.last l'.len) :
    (map a b).toOrderHom (Fin.last (common k l).len) = Fin.last (common k' l').len := by
  have h := SimplexCategory.congr_toOrderHom_apply (rightIn_map a b) (Fin.last l.len)
  change (map a b).toOrderHom ((rightIn k l).toOrderHom (Fin.last l.len)) =
    (rightIn k' l').toOrderHom (b.toOrderHom (Fin.last l.len)) at h
  rw [hb, rightIn_last, rightIn_last] at h
  exact h

end DaggerModels.PartII.JTParameterBlockOperators
