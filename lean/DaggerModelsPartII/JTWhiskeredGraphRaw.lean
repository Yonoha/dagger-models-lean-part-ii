import DaggerModelsPartII.JTActualJointChainSideRaw
import DaggerModelsPartII.JTThreePieceLabelOperators

/-! Glue exact raw equations on the full native inverse images of a graph domain. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTWhiskeredGraphRaw

open JTNecklaceLabelRealization (realizedLabel)
open TripleBeadEndpointLabel (labels glue glue_left glue_right)
open ReversalDiscreteFreeColimits (discreteFree)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev std := SSet.stdSimplex.{0}
private abbrev J := GroupoidSimplex.parameter
private abbrev pre (W : Source) {X Y : SSet.{0}} (i : X ⟶ Y) :=
  diagramMappingPrecomp (discreteFree.map i) W

variable (W : Source) {X : SSet.{0}} {T S : NecklaceCode} {k : SimplexCategory}

/-- Restriction to the entire inverse image of any native piece retains
the complete graph coefficient, with no product-domain assumption. -/
theorem piece_restrict (h : X ⟶ T.toSSet) (p : X ⟶ J.obj k)
    (i : S.toSSet ⟶ T.toSSet) (c : std.obj k ⟶ labels W T)
    (d : std.obj k ⟶ labels W S) (hc : c ≫ pre W i = d) :
    pullback.fst h i ≫ (lift h p ≫ realizedLabel T.toSSet W k (SSet.yonedaEquiv c)) =
      lift (pullback.snd h i) (pullback.fst h i ≫ p) ≫
        realizedLabel S.toSSet W k (SSet.yonedaEquiv d) := by
  rw [← Category.assoc, comp_lift, pullback.condition]
  simpa only [hc] using JTWhiskerEdgeGraphRaw.native_restrict W i
    (pullback.snd h i) (pullback.fst h i ≫ p) c

variable {U : NecklaceCode}

/-- Raw equations on both full native inverse images imply the exact
whole-label raw equation over the same specified raw target. -/
theorem binary_raw (h : X ⟶ (wedge T U).toSSet) (p : X ⟶ J.obj k)
    (c : std.obj k ⟶ labels W T) (d : std.obj k ⟶ labels W U)
    (hc : c ≫ TripleBeadEndpointLabel.lastRestriction W T =
      d ≫ TripleBeadEndpointLabel.firstRestriction W U)
    (g : (wedge T U).toSSet ⟶ Raw W)
    (hl : lift (pullback.snd h (wedgeιLeft T U))
        (pullback.fst h (wedgeιLeft T U) ≫ p) ≫
          realizedLabel T.toSSet W k (SSet.yonedaEquiv c) =
      pullback.snd h (wedgeιLeft T U) ≫ wedgeιLeft T U ≫ g)
    (hr : lift (pullback.snd h (wedgeιRight T U))
        (pullback.fst h (wedgeιRight T U) ≫ p) ≫
          realizedLabel U.toSSet W k (SSet.yonedaEquiv d) =
      pullback.snd h (wedgeιRight T U) ≫ wedgeιRight T U ≫ g) :
    lift h p ≫ realizedLabel (wedge T U).toSSet W k
        (SSet.yonedaEquiv (glue W T U k c d hc)) = h ≫ g := by
  apply JTActualJointChainSideRaw.binary_hom_ext h
  · rw [piece_restrict W h p (wedgeιLeft T U) _ c (glue_left W T U k c d hc), hl]
    simp only [← Category.assoc, pullback.condition]
  · rw [piece_restrict W h p (wedgeιRight T U) _ d (glue_right W T U k c d hc), hr]
    simp only [← Category.assoc, pullback.condition]

private theorem nested_piece_eq {A B C X Y : SSet.{0}}
    (h : X ⟶ C) (i : A ⟶ B) (j : B ⟶ C) {f g : X ⟶ Y}
    (he : pullback.fst h (i ≫ j) ≫ f = pullback.fst h (i ≫ j) ≫ g) :
    pullback.fst (pullback.snd h j) i ≫ (pullback.fst h j ≫ f) =
      pullback.fst (pullback.snd h j) i ≫ (pullback.fst h j ≫ g) := by
  let a := pullback.fst (pullback.snd h j) i ≫ pullback.fst h j
  let b := pullback.snd (pullback.snd h j) i
  have hab : a ≫ h = b ≫ (i ≫ j) := by
    dsimp only [a, b]
    rw [Category.assoc, pullback.condition, ← Category.assoc,
      pullback.condition, Category.assoc]
  let v := pullback.lift a b hab
  have hv : v ≫ pullback.fst h (i ≫ j) = a := pullback.lift_fst _ _ _
  have ht := congrArg (v ≫ ·) he
  simpa only [← Category.assoc, hv, a] using ht

/-- All three full native inverse images detect equality on arbitrary
surrounding necklaces, including changes in their lengths. -/
theorem triple_hom_ext {P M R : NecklaceCode} {X Y : SSet.{0}}
    (h : X ⟶ (wedge P (wedge M R)).toSSet) {f g : X ⟶ Y}
    (hl : pullback.fst h (tripleRightT P M R) ≫ f =
      pullback.fst h (tripleRightT P M R) ≫ g)
    (hm : pullback.fst h (tripleRightU P M R) ≫ f =
      pullback.fst h (tripleRightU P M R) ≫ g)
    (hr : pullback.fst h (tripleRightV P M R) ≫ f =
      pullback.fst h (tripleRightV P M R) ≫ g) : f = g := by
  apply JTActualJointChainSideRaw.binary_hom_ext h hl
  apply JTActualJointChainSideRaw.binary_hom_ext (pullback.snd h (wedgeιRight P (wedge M R)))
  · exact nested_piece_eq h (wedgeιLeft M R) (wedgeιRight P (wedge M R)) hm
  · exact nested_piece_eq h (wedgeιRight M R) (wedgeιRight P (wedge M R)) hr

private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)

variable {P M R : NecklaceCode} {x y : Vertex W}
variable (C : JTThreePieceLabelOperators.Data W P M R k x y)

private abbrev coefficient :=
  JTComposedPrismLabels.coefficient (JTThreePieceLabelOperators.coefficients C)

theorem coefficient_left : coefficient W C ≫ pre W (tripleRightT P M R) = C.left :=
  glue_left W P (wedge M R) k C.left (JTThreePieceLabelOperators.inside C)
    (JTThreePieceLabelOperators.coefficients C).seam

theorem coefficient_middle : coefficient W C ≫ pre W (tripleRightU P M R) = C.middle := by
  unfold coefficient JTComposedPrismLabels.coefficient pre tripleRightU
  rw [discreteFree.map_comp, diagramMappingPrecomp_comp, ← Category.assoc, glue_right]
  exact glue_left W M R k C.middle C.right C.right_join

theorem coefficient_right : coefficient W C ≫ pre W (tripleRightV P M R) = C.right := by
  unfold coefficient JTComposedPrismLabels.coefficient pre tripleRightV
  rw [discreteFree.map_comp, diagramMappingPrecomp_comp, ← Category.assoc, glue_right]
  exact glue_right W M R k C.middle C.right C.right_join

/-- Exact raw values on the three complete graph pieces give the whole
whiskered raw equation in the same specified target. -/
theorem triple_raw (h : X ⟶ (wedge P (wedge M R)).toSSet) (p : X ⟶ J.obj k)
    (g : (wedge P (wedge M R)).toSSet ⟶ Raw W)
    (hl : lift (pullback.snd h (tripleRightT P M R))
        (pullback.fst h (tripleRightT P M R) ≫ p) ≫
          realizedLabel P.toSSet W k (SSet.yonedaEquiv C.left) =
      pullback.snd h (tripleRightT P M R) ≫ tripleRightT P M R ≫ g)
    (hm : lift (pullback.snd h (tripleRightU P M R))
        (pullback.fst h (tripleRightU P M R) ≫ p) ≫
          realizedLabel M.toSSet W k (SSet.yonedaEquiv C.middle) =
      pullback.snd h (tripleRightU P M R) ≫ tripleRightU P M R ≫ g)
    (hr : lift (pullback.snd h (tripleRightV P M R))
        (pullback.fst h (tripleRightV P M R) ≫ p) ≫
          realizedLabel R.toSSet W k (SSet.yonedaEquiv C.right) =
      pullback.snd h (tripleRightV P M R) ≫ tripleRightV P M R ≫ g) :
    lift h p ≫ realizedLabel (wedge P (wedge M R)).toSSet W k
        (SSet.yonedaEquiv (coefficient W C)) = h ≫ g := by
  apply triple_hom_ext h
  · rw [piece_restrict W h p (tripleRightT P M R) _ C.left (coefficient_left W C), hl]
    simp only [← Category.assoc, pullback.condition]
  · rw [piece_restrict W h p (tripleRightU P M R) _ C.middle (coefficient_middle W C), hm]
    simp only [← Category.assoc, pullback.condition]
  · rw [piece_restrict W h p (tripleRightV P M R) _ C.right (coefficient_right W C), hr]
    simp only [← Category.assoc, pullback.condition]

/-- The three exact raw equations on the full inverse-image native pieces.
They refer to one graph domain, coefficient parameter and specified raw target. -/
structure PieceEquations (h : X ⟶ (wedge P (wedge M R)).toSSet)
    (p : X ⟶ J.obj k) (g : (wedge P (wedge M R)).toSSet ⟶ Raw W) : Prop where
  left : lift (pullback.snd h (tripleRightT P M R))
      (pullback.fst h (tripleRightT P M R) ≫ p) ≫
        realizedLabel P.toSSet W k (SSet.yonedaEquiv C.left) =
    pullback.snd h (tripleRightT P M R) ≫ tripleRightT P M R ≫ g
  middle : lift (pullback.snd h (tripleRightU P M R))
      (pullback.fst h (tripleRightU P M R) ≫ p) ≫
        realizedLabel M.toSSet W k (SSet.yonedaEquiv C.middle) =
    pullback.snd h (tripleRightU P M R) ≫ tripleRightU P M R ≫ g
  right : lift (pullback.snd h (tripleRightV P M R))
      (pullback.fst h (tripleRightV P M R) ≫ p) ≫
        realizedLabel R.toSSet W k (SSet.yonedaEquiv C.right) =
    pullback.snd h (tripleRightV P M R) ≫ tripleRightV P M R ≫ g

theorem PieceEquations.raw {h : X ⟶ (wedge P (wedge M R)).toSSet}
    {p : X ⟶ J.obj k} {g : (wedge P (wedge M R)).toSSet ⟶ Raw W}
    (H : PieceEquations W C h p g) :
    lift h p ≫ realizedLabel (wedge P (wedge M R)).toSSet W k
      (SSet.yonedaEquiv (coefficient W C)) = h ≫ g :=
  triple_raw W C h p g H.left H.middle H.right

/-- The raw equation is for the actual ordered decorated label, not only
for an auxiliary unordered mapping-space coefficient. -/
theorem PieceEquations.ordered_raw {h : X ⟶ (wedge P (wedge M R)).toSSet}
    {p : X ⟶ J.obj k} {g : (wedge P (wedge M R)).toSSet ⟶ Raw W}
    (H : PieceEquations W C h p g) :
    lift h p ≫ realizedLabel (wedge P (wedge M R)).toSSet W k
      (JTRealizedLabelEndpoints.orderedLabel W x y (wedge P (wedge M R)) k
        (JTComposedPrismLabels.orderedPoint (JTThreePieceLabelOperators.coefficients C))) =
      h ≫ g := by
  rw [JTComposedPrismLabels.orderedPoint_coefficient]
  exact PieceEquations.raw W C H

end

end DaggerModels.PartII.JTWhiskeredGraphRaw
