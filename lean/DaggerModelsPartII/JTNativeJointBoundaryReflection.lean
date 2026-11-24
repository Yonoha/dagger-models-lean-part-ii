import OriginalFlagJointOrder
import ChosenNecklacePointMaps
import ChosenNecklaceMapInclusion

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerOriginalFlagFlankification

namespace DaggerModels.PartII.JTNativeJointBoundaryReflection

noncomputable section

private theorem bead_constant_zero {T L : NecklaceCode} (f : T ⟶ L)
    (b : T.Bead) (h : orderMap f.map b.right = 0) :
    T.beadSimplex b ≫ f.map =
      SSet.stdSimplex.isTerminalObj₀.from Δ[b.length] ≫ pointAt L (ULift.up 0) := by
  have ht : SSet.stdSimplex.isTerminalObj₀.from Δ[b.length] =
      SSet.stdSimplex.map (SimplexCategory.const ⦋b.length⦌ ⦋0⦌ 0) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [ht]
  apply (cancel_mono L.inclusion).1
  rw [Category.assoc, map_inclusion, ← Category.assoc]
  apply stdSimplex_hom_ext
  intro x
  apply SSet.stdSimplex.ext
  intro i
  have hv : orderMap f.map (b.embedding (x i)) = 0 := by
    apply le_antisymm
    · rw [← h]
      exact (orderMap f.map).monotone (by rw [← b.embedding_last]; exact b.embedding.monotone (Fin.le_last _))
    · exact Fin.zero_le _
  change orderMap f.map ((T.inclusion.app _ (T.beadSimplex b |>.app _ x)) i) =
    (L.inclusion.app _
    ((pointAt L (ULift.up 0)).app _
      ((SSet.stdSimplex.map (SimplexCategory.const ⦋b.length⦌ ⦋0⦌ 0)).app _ x))) i
  rw [b.beadSimplex_inclusion_apply, pointAt_inclusion_apply]
  exact hv

private theorem bead_constant_last {T L : NecklaceCode} (f : T ⟶ L)
    (b : T.Bead) (h : orderMap f.map b.left = Fin.last L.len) :
    T.beadSimplex b ≫ f.map =
      SSet.stdSimplex.isTerminalObj₀.from Δ[b.length] ≫
        pointAt L (ULift.up (Fin.last L.len)) := by
  have ht : SSet.stdSimplex.isTerminalObj₀.from Δ[b.length] =
      SSet.stdSimplex.map (SimplexCategory.const ⦋b.length⦌ ⦋0⦌ 0) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [ht]
  apply (cancel_mono L.inclusion).1
  rw [Category.assoc, map_inclusion, ← Category.assoc]
  apply stdSimplex_hom_ext
  intro x
  apply SSet.stdSimplex.ext
  intro i
  have hv : orderMap f.map (b.embedding (x i)) = Fin.last L.len := by
    apply le_antisymm
    · exact Fin.le_last _
    · rw [← h]
      exact (orderMap f.map).monotone (by rw [← b.embedding_zero]; exact b.embedding.monotone (Fin.zero_le _))
  change orderMap f.map ((T.inclusion.app _ (T.beadSimplex b |>.app _ x)) i) =
    (L.inclusion.app _
    ((pointAt L (ULift.up (Fin.last L.len))).app _
      ((SSet.stdSimplex.map (SimplexCategory.const ⦋b.length⦌ ⦋0⦌ 0)).app _ x))) i
  rw [b.beadSimplex_inclusion_apply, pointAt_inclusion_apply]
  exact hv

theorem joint_eq_first_of_map_first {T L : NecklaceCode} (f : T ⟶ L)
    (hfirst : ∀ b : T.Bead, T.beadSimplex b ≫ f.map ≠
      SSet.stdSimplex.isTerminalObj₀.from Δ[b.length] ≫ pointAt L (ULift.up 0))
    (v : Fin (T.len + 1)) (hv : v ∈ T.joints)
    (h : orderMap f.map v = 0) : v = 0 := by
  let j := jointIndex T v hv
  by_contra hn
  have hj : 0 < j.val := by
    by_contra hzero
    have hz : j = 0 := by
      apply Fin.ext
      exact Nat.eq_zero_of_not_pos hzero
    have he := jointEmbedding_jointIndex T v hv
    change jointEmbedding T j = v at he
    rw [hz, jointEmbedding_first] at he
    exact hn he.symm
  let i : Fin (beadCount T) := ⟨j.val - 1, by have hjlt := j.isLt; omega⟩
  have hi : i.succ = j := by apply Fin.ext; change i.val + 1 = j.val; dsimp [i]; omega
  let b := jointBead T i
  have hb : b.right = v := by
    change jointEmbedding T i.succ = v
    rw [hi, jointEmbedding_jointIndex]
  exact hfirst b (bead_constant_zero f b (hb ▸ h))

theorem joint_eq_last_of_map_last {T L : NecklaceCode} (f : T ⟶ L)
    (hlast : ∀ b : T.Bead, T.beadSimplex b ≫ f.map ≠
      SSet.stdSimplex.isTerminalObj₀.from Δ[b.length] ≫
        pointAt L (ULift.up (Fin.last L.len)))
    (v : Fin (T.len + 1)) (hv : v ∈ T.joints)
    (h : orderMap f.map v = Fin.last L.len) : v = Fin.last T.len := by
  let j := jointIndex T v hv
  by_contra hn
  have hj : j.val < beadCount T := by
    by_contra hnot
    have hz : j = Fin.last (beadCount T) := by
      apply Fin.ext
      have hjlt := j.isLt
      change j.val = beadCount T
      omega
    have he := jointEmbedding_jointIndex T v hv
    change jointEmbedding T j = v at he
    rw [hz, jointEmbedding_last] at he
    exact hn he.symm
  let i : Fin (beadCount T) := ⟨j.val, hj⟩
  have hi : i.castSucc = j := by apply Fin.ext; rfl
  let b := jointBead T i
  have hb : b.left = v := by
    change jointEmbedding T i.castSucc = v
    rw [hi, jointEmbedding_jointIndex]
  exact hlast b (bead_constant_last f b (hb ▸ h))

end

end DaggerModels.PartII.JTNativeJointBoundaryReflection
