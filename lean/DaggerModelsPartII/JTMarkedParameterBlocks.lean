import DaggerModelsPartII.JTParameterBlockOperators

/-! Marked coefficient retractions that commute with arbitrary block operators. -/

set_option autoImplicit false

open CategoryTheory Simplicial

namespace DaggerModels.PartII.JTMarkedParameterBlocks

open JTParameterBlocks
open JTParameterBlockOperators (map leftIn_map_assoc rightIn_map_assoc
  rightIn_leftRet leftIn_rightRet)

noncomputable section

/-- Clip the left parameter to the part at or below its marked vertex. -/
def leftClip (k : SimplexCategory) (i : Fin (k.len + 1)) : k ⟶ k :=
  SimplexCategory.Hom.mk ⟨fun u ↦ min u i, monotone_id.min monotone_const⟩

/-- Clip the right parameter to the part at or above its marked vertex. -/
def rightClip (l : SimplexCategory) (j : Fin (l.len + 1)) : l ⟶ l :=
  SimplexCategory.Hom.mk ⟨fun u ↦ max u j, monotone_id.max monotone_const⟩

/-- Extend a clipped left parameter by the marked left vertex on the right block. -/
def leftMarked (k l : SimplexCategory) (i : Fin (k.len + 1)) : common k l ⟶ k :=
  leftRet k l ≫ leftClip k i

/-- Extend a clipped right parameter by the marked right vertex on the left block. -/
def rightMarked (k l : SimplexCategory) (j : Fin (l.len + 1)) : common k l ⟶ l :=
  rightRet k l ≫ rightClip l j

variable {k l k' l' : SimplexCategory}

theorem leftClip_map (a : k ⟶ k') (i : Fin (k.len + 1)) :
    leftClip k i ≫ a = a ≫ leftClip k' (a.toOrderHom i) := by
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro u
  exact a.toOrderHom.monotone.map_min

theorem rightClip_map (b : l ⟶ l') (j : Fin (l.len + 1)) :
    rightClip l j ≫ b = b ≫ rightClip l' (b.toOrderHom j) := by
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro u
  exact b.toOrderHom.monotone.map_max

theorem leftIn_leftMarked (i : Fin (k.len + 1)) :
    leftIn k l ≫ leftMarked k l i = leftClip k i := by
  rw [leftMarked, ← Category.assoc, left_split, Category.id_comp]

theorem rightIn_rightMarked (j : Fin (l.len + 1)) :
    rightIn k l ≫ rightMarked k l j = rightClip l j := by
  rw [rightMarked, ← Category.assoc, right_split, Category.id_comp]

theorem rightIn_leftMarked (i : Fin (k.len + 1)) :
    rightIn k l ≫ leftMarked k l i = SimplexCategory.const l k i := by
  rw [leftMarked, ← Category.assoc, rightIn_leftRet, SimplexCategory.const_comp]
  congr 1
  exact min_eq_right (Fin.le_last i)

theorem leftIn_rightMarked (j : Fin (l.len + 1)) :
    leftIn k l ≫ rightMarked k l j = SimplexCategory.const k l j := by
  rw [rightMarked, ← Category.assoc, leftIn_rightRet, SimplexCategory.const_comp]
  congr 1

/-- An arbitrary ordinal operator transports the marked left vertex exactly. -/
theorem leftMarked_map (a : k ⟶ k') (b : l ⟶ l') (i : Fin (k.len + 1)) :
    leftMarked k l i ≫ a = map a b ≫ leftMarked k' l' (a.toOrderHom i) := by
  apply JTParameterBlockOperators.hom_ext
  · rw [← Category.assoc, leftIn_leftMarked, leftIn_map_assoc, leftIn_leftMarked, leftClip_map]
  · rw [← Category.assoc, rightIn_leftMarked, SimplexCategory.const_comp,
      rightIn_map_assoc, rightIn_leftMarked]
    rfl

/-- An arbitrary ordinal operator transports the marked right vertex exactly. -/
theorem rightMarked_map (a : k ⟶ k') (b : l ⟶ l') (j : Fin (l.len + 1)) :
    rightMarked k l j ≫ b = map a b ≫ rightMarked k' l' (b.toOrderHom j) := by
  apply JTParameterBlockOperators.hom_ext
  · rw [← Category.assoc, leftIn_rightMarked, SimplexCategory.const_comp,
      leftIn_map_assoc, leftIn_rightMarked]
    rfl
  · rw [← Category.assoc, rightIn_rightMarked, rightIn_map_assoc, rightIn_rightMarked, rightClip_map]

end

end DaggerModels.PartII.JTMarkedParameterBlocks
