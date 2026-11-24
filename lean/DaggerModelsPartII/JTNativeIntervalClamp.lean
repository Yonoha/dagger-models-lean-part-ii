import ChosenNecklaceCutDegree
import ChosenNecklaceOrderMaps

/-!
# Native interval clamps

The ambient order lifts below factor through the actual interval necklaces.
They make no pushout claim about the plateau quotient of a bead.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTNativeIntervalClamp

noncomputable section

variable (T : NecklaceCode) (c : Fin (T.len + 1))

private def leftOrder : Fin (T.len + 1) →o Fin (T.len + 1) where
  toFun v := min v c
  monotone' := by
    intro v w h
    exact min_le_min h le_rfl

private def rightOrder : Fin (T.len + 1) →o Fin (T.len + 1) where
  toFun v := max v c
  monotone' := by
    intro v w h
    exact max_le_max h le_rfl

private theorem leftBeadImage : BeadImageCondition (leftOrder T c) := by
  intro b
  by_cases h : b.left ≤ c
  · left
    refine ⟨b, ?_⟩
    intro v hv
    obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp hv
    exact Finset.mem_Icc.mpr ⟨le_min hl h, (min_le_left v c).trans hr⟩
  · right
    refine ⟨c, ?_⟩
    intro v hv
    have hcv : c ≤ v := (lt_of_not_ge h).le.trans (Finset.mem_Icc.mp hv).1
    exact min_eq_right hcv

private theorem rightBeadImage : BeadImageCondition (rightOrder T c) := by
  intro b
  by_cases h : c ≤ b.right
  · left
    refine ⟨b, ?_⟩
    intro v hv
    obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp hv
    exact Finset.mem_Icc.mpr ⟨hl.trans (le_max_left v c), max_le hr h⟩
  · right
    refine ⟨c, ?_⟩
    intro v hv
    have hvc : v ≤ c := (Finset.mem_Icc.mp hv).2.trans (lt_of_not_ge h).le
    exact max_eq_right hvc

private def leftAmbient : T.toSSet ⟶ T.toSSet :=
  orderLift (leftOrder T c) (leftBeadImage T c)

private def rightAmbient : T.toSSet ⟶ T.toSSet :=
  orderLift (rightOrder T c) (rightBeadImage T c)

theorem leftAmbient_vertices (v : Vertices.{0} T) :
    mapVertices (leftAmbient T c) v = ULift.up (min v.down c) :=
  orderLift_vertices (leftOrder T c) (leftBeadImage T c) v

theorem rightAmbient_vertices (v : Vertices.{0} T) :
    mapVertices (rightAmbient T c) v = ULift.up (max v.down c) :=
  orderLift_vertices (rightOrder T c) (rightBeadImage T c) v

private theorem leftBounds (x : (toSSet.{0} T).obj (op ⦋0⦌)) :
    (0 : Fin (T.len + 1)) ≤ T.inclusion.app _ ((leftAmbient T c).app _ x) 0 ∧
      T.inclusion.app _ ((leftAmbient T c).app _ x) 0 ≤ c := by
  have h := congrArg ULift.down (leftAmbient_vertices T c (T.verticesEquiv x))
  simp only [mapVertices, Equiv.symm_apply_apply] at h
  change (T.verticesEquiv ((leftAmbient T c).app _ x)).down =
    min (T.verticesEquiv x).down c at h
  rw [T.verticesEquiv_down, T.verticesEquiv_down] at h
  change T.inclusion.app _ ((leftAmbient T c).app _ x) 0 =
    min (T.inclusion.app _ x 0) c at h
  rw [h]
  exact ⟨Fin.zero_le _, min_le_right _ _⟩

private theorem rightBounds (x : (toSSet.{0} T).obj (op ⦋0⦌)) :
    c ≤ T.inclusion.app _ ((rightAmbient T c).app _ x) 0 ∧
      T.inclusion.app _ ((rightAmbient T c).app _ x) 0 ≤ Fin.last T.len := by
  have h := congrArg ULift.down (rightAmbient_vertices T c (T.verticesEquiv x))
  simp only [mapVertices, Equiv.symm_apply_apply] at h
  change (T.verticesEquiv ((rightAmbient T c).app _ x)).down =
    max (T.verticesEquiv x).down c at h
  rw [T.verticesEquiv_down, T.verticesEquiv_down] at h
  change T.inclusion.app _ ((rightAmbient T c).app _ x) 0 =
    max (T.inclusion.app _ x 0) c at h
  rw [h]
  exact ⟨le_max_right _ _, Fin.le_last _⟩

/-- The left clamp lands in the native clipped necklace. -/
def leftClamp : T.toSSet ⟶ (cutLeft T c).toSSet :=
  intervalFactor T 0 c (Fin.zero_le c) (leftAmbient T c) (leftBounds T c)

/-- The right clamp lands in the native clipped necklace. -/
def rightClamp : T.toSSet ⟶ (cutRight T c).toSSet :=
  intervalFactor T c (Fin.last T.len) (Fin.le_last c)
    (rightAmbient T c) (rightBounds T c)

theorem leftClamp_fac : leftClamp T c ≫ cutLeftι T c = leftAmbient T c :=
  intervalFactor_fac T 0 c (Fin.zero_le c) (leftAmbient T c) (leftBounds T c)

theorem rightClamp_fac : rightClamp T c ≫ cutRightι T c = rightAmbient T c :=
  intervalFactor_fac T c (Fin.last T.len) (Fin.le_last c)
    (rightAmbient T c) (rightBounds T c)

theorem leftClamp_vertices (v : Vertices.{0} T) :
    mapVertices (leftClamp T c ≫ cutLeftι T c) v = ULift.up (min v.down c) := by
  rw [leftClamp_fac]
  exact leftAmbient_vertices T c v

theorem rightClamp_vertices (v : Vertices.{0} T) :
    mapVertices (rightClamp T c ≫ cutRightι T c) v = ULift.up (max v.down c) := by
  rw [rightClamp_fac]
  exact rightAmbient_vertices T c v

theorem leftClamp_orderMap (v : Fin (T.len + 1)) :
    orderMap (leftClamp T c ≫ cutLeftι T c) v = min v c := by
  exact congrArg ULift.down (leftClamp_vertices T c (ULift.up v))

theorem rightClamp_orderMap (v : Fin (T.len + 1)) :
    orderMap (rightClamp T c ≫ cutRightι T c) v = max v c := by
  exact congrArg ULift.down (rightClamp_vertices T c (ULift.up v))

end

end DaggerModels.PartII.JTNativeIntervalClamp
