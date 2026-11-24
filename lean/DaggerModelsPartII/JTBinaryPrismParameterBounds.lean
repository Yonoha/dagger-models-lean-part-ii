import DaggerModelsPartII.JTBinaryPrismTargetLift
import DaggerModelsPartII.JTCodiscreteParameterPairing
import DaggerModelsPartII.JTMarkedParameterBlocks

/-! Coordinate bounds for the complete joined binary prism parameter. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTBinaryPrismParameterBounds

open JTCodiscreteParameterPairing (coord coord_map)
open JTParameterBlocks (common leftIn rightIn leftPoint rightPoint leftPoint_lt_rightPoint)
open JTMarkedParameterBlocks (leftClip rightClip)

noncomputable section

private abbrev J := GroupoidSimplex.parameter

private theorem lower_clip_fixed {X : SSet.{0}} {a : SimplexCategory}
    (p : X ⟶ J.obj a) (i : Fin (a.len + 1))
    (h : ∀ q z v, i ≤ coord a q (p.app q z) v) :
    p ≫ J.map (rightClip a i) = p := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z v
  change coord a q ((J.map (rightClip a i)).app q (p.app q z)) v = _
  rw [coord_map]
  exact max_eq_left (h q z v)

private theorem upper_clip_fixed {X : SSet.{0}} {a : SimplexCategory}
    (p : X ⟶ J.obj a) (i : Fin (a.len + 1))
    (h : ∀ q z v, coord a q (p.app q z) v ≤ i) :
    p ≫ J.map (leftClip a i) = p := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z v
  change coord a q ((J.map (leftClip a i)).app q (p.app q z)) v = _
  rw [coord_map]
  exact min_eq_left (h q z v)

private theorem lower_of_clip_fixed {X : SSet.{0}} {a : SimplexCategory}
    (p : X ⟶ J.obj a) (i : Fin (a.len + 1))
    (h : p ≫ J.map (rightClip a i) = p) :
    ∀ q z v, i ≤ coord a q (p.app q z) v := by
  intro q z v
  have e := congrArg (fun f : X ⟶ J.obj a ↦ coord a q (f.app q z) v) h
  change coord a q ((J.map (rightClip a i)).app q (p.app q z)) v = _ at e
  rw [coord_map] at e
  change max (coord a q (p.app q z) v) i = coord a q (p.app q z) v at e
  rw [← e]
  exact le_max_right _ _

private theorem upper_of_clip_fixed {X : SSet.{0}} {a : SimplexCategory}
    (p : X ⟶ J.obj a) (i : Fin (a.len + 1))
    (h : p ≫ J.map (leftClip a i) = p) :
    ∀ q z v, coord a q (p.app q z) v ≤ i := by
  intro q z v
  have e := congrArg (fun f : X ⟶ J.obj a ↦ coord a q (f.app q z) v) h
  change coord a q ((J.map (leftClip a i)).app q (p.app q z)) v = _ at e
  rw [coord_map] at e
  change min (coord a q (p.app q z) v) i = coord a q (p.app q z) v at e
  rw [← e]
  exact min_le_right _ _

variable {T U : DaggerChosenRigidificationNecklace.NecklaceCode}
variable {k l n : SimplexCategory}
variable (s : T.toSSet ⊗ J.obj n ⟶ J.obj k)
variable (t : U.toSSet ⊗ J.obj n ⟶ J.obj l)

/-- A lower bound on every left input coordinate bounds the entire joined parameter,
including the time-dependent connector. -/
theorem parameter_lower_bound (i : Fin (k.len + 1))
    (hs : ∀ q z v, i ≤ coord k q (s.app q z) v) :
    ∀ q z v, (leftIn k l).toOrderHom i ≤
      coord (common k l) q ((JTBinaryPrismTargetLift.parameter s t).app q z) v := by
  let p := JTBinaryPrismTargetLift.parameter s t
  let c := rightClip (common k l) ((leftIn k l).toOrderHom i)
  have hleft : ∀ q z v, (leftIn k l).toOrderHom i ≤
      coord (common k l) q ((s ≫ J.map (leftIn k l)).app q z) v := by
    intro q z v
    change _ ≤ coord (common k l) q
      ((J.map (leftIn k l)).app q (s.app q z)) v
    rw [coord_map]
    exact (leftIn k l).toOrderHom.monotone (hs q z v)
  have hright : ∀ q z v, (leftIn k l).toOrderHom i ≤
      coord (common k l) q ((t ≫ J.map (rightIn k l)).app q z) v := by
    intro q z v
    change _ ≤ coord (common k l) q
      ((J.map (rightIn k l)).app q (t.app q z)) v
    rw [coord_map]
    exact le_of_lt (leftPoint_lt_rightPoint k l i (coord l q (t.app q z) v))
  have hsl := lower_clip_fixed (s ≫ J.map (leftIn k l)) _ hleft
  have htr := lower_clip_fixed (t ≫ J.map (rightIn k l)) _ hright
  have hp : p ≫ J.map c = p := by
    change JTBinaryPrismParameter.parameter T U (common k l) (J.obj n)
      (s ≫ J.map (leftIn k l)) (t ≫ J.map (rightIn k l)) ≫ J.map c = _
    rw [JTBinaryPrismParameter.parameter_postcomp, hsl, htr]
    rfl
  exact lower_of_clip_fixed p _ hp

/-- An upper bound on every right input coordinate bounds the entire joined parameter,
including the time-dependent connector. -/
theorem parameter_upper_bound (j : Fin (l.len + 1))
    (ht : ∀ q z v, coord l q (t.app q z) v ≤ j) :
    ∀ q z v, coord (common k l) q
      ((JTBinaryPrismTargetLift.parameter s t).app q z) v ≤
        (rightIn k l).toOrderHom j := by
  let p := JTBinaryPrismTargetLift.parameter s t
  let c := leftClip (common k l) ((rightIn k l).toOrderHom j)
  have hleft : ∀ q z v,
      coord (common k l) q ((s ≫ J.map (leftIn k l)).app q z) v ≤
        (rightIn k l).toOrderHom j := by
    intro q z v
    change coord (common k l) q
      ((J.map (leftIn k l)).app q (s.app q z)) v ≤ _
    rw [coord_map]
    exact le_of_lt (leftPoint_lt_rightPoint k l (coord k q (s.app q z) v) j)
  have hright : ∀ q z v,
      coord (common k l) q ((t ≫ J.map (rightIn k l)).app q z) v ≤
        (rightIn k l).toOrderHom j := by
    intro q z v
    change coord (common k l) q
      ((J.map (rightIn k l)).app q (t.app q z)) v ≤ _
    rw [coord_map]
    exact (rightIn k l).toOrderHom.monotone (ht q z v)
  have hsl := upper_clip_fixed (s ≫ J.map (leftIn k l)) _ hleft
  have htr := upper_clip_fixed (t ≫ J.map (rightIn k l)) _ hright
  have hp : p ≫ J.map c = p := by
    change JTBinaryPrismParameter.parameter T U (common k l) (J.obj n)
      (s ≫ J.map (leftIn k l)) (t ≫ J.map (rightIn k l)) ≫ J.map c = _
    rw [JTBinaryPrismParameter.parameter_postcomp, hsl, htr]
    rfl
  exact upper_of_clip_fixed p _ hp

end

end DaggerModels.PartII.JTBinaryPrismParameterBounds
