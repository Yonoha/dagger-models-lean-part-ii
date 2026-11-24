import DaggerModelsPartII.TwoBeadEndpointLabel
import DaggerModelsPartII.JTRealizedLabelEndpoints
import DaggerModelsPartII.JTNecklaceLabelRealization
import DaggerModelsPartII.DiagramMappingPushout
import DaggerModelsPartII.ReversalDiscreteFreeColimits
import ChosenNecklaceTripleWedge
import ChosenNecklaceWedgePushout

/-!
# A complete ordered label on an arbitrary three-bead native necklace

The native code is `wedge (single 1) (wedge (single d) (single 1))`.
Three complete `Δ[k]`-parameter families glue by the two actual necklace
pushouts. Both joint equations and both outer endpoint equations hold on
the whole parameter. No target finality or raw-edge representation follows.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.TripleBeadEndpointLabel

open ReversalDiscreteFreeColimits OrderedNecklaceLabelDiagram

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev F := discreteFree.{0}
private abbrev NCode := DaggerChosenRigidificationNecklace.NecklaceCode
private abbrev K (k : SimplexCategory) : SSet.{0} := SSet.stdSimplex.obj k

/-- The actual three-bead code, including the middle bead of length zero. -/
def code (d : ℕ) : NCode :=
  wedge (single 1) (wedge (single d) (single 1))

def labels (W : Source) (T : NCode) : SSet.{0} :=
  diagramMappingSpace (F.obj T.toSSet) W

def pointLabels (W : Source) : SSet.{0} :=
  diagramMappingSpace (F.obj (Δ[0] : SSet.{0})) W

def firstRestriction (W : Source) (T : NCode) :
    labels W T ⟶ pointLabels W :=
  diagramMappingPrecomp (F.map (pointAt T (ULift.up 0))) W

def lastRestriction (W : Source) (T : NCode) :
    labels W T ⟶ pointLabels W :=
  diagramMappingPrecomp (F.map (pointAt T (ULift.up (Fin.last T.len)))) W

/-- The generic native wedge pushout, mapped into strict diagram labels. -/
def wedgeMappingPullback (W : Source) (T U : NCode) :
    IsPullback
      (diagramMappingPrecomp (F.map (wedgeιLeft T U)) W)
      (diagramMappingPrecomp (F.map (wedgeιRight T U)) W)
      (lastRestriction W T) (firstRestriction W U) :=
  diagramMappingSpace_isPullback
    (ReversalDiscreteFreeColimits.map_isPushout (wedgeIsPushout T U)) W

def glue (W : Source) (T U : NCode) (k : SimplexCategory)
    (a : K k ⟶ labels W T) (b : K k ⟶ labels W U)
    (h : a ≫ lastRestriction W T = b ≫ firstRestriction W U) :
    K k ⟶ labels W (wedge T U) :=
  (wedgeMappingPullback W T U).lift a b h

theorem glue_left (W : Source) (T U : NCode) (k : SimplexCategory)
    (a : K k ⟶ labels W T) (b : K k ⟶ labels W U)
    (h : a ≫ lastRestriction W T = b ≫ firstRestriction W U) :
    glue W T U k a b h ≫
        diagramMappingPrecomp (F.map (wedgeιLeft T U)) W = a :=
  (wedgeMappingPullback W T U).lift_fst a b h

theorem glue_right (W : Source) (T U : NCode) (k : SimplexCategory)
    (a : K k ⟶ labels W T) (b : K k ⟶ labels W U)
    (h : a ≫ lastRestriction W T = b ≫ firstRestriction W U) :
    glue W T U k a b h ≫
        diagramMappingPrecomp (F.map (wedgeιRight T U)) W = b :=
  (wedgeMappingPullback W T U).lift_snd a b h

private theorem firstVertex_wedge (T U : NCode) :
    pointAt T (ULift.up 0) ≫ wedgeιLeft T U =
      SSet.yonedaEquiv.symm (wedge T U).first := by
  apply SSet.yonedaEquiv.injective
  simpa only [SSet.yonedaEquiv_comp, pointAt_vertex,
    Equiv.apply_symm_apply, first] using (wedgeιLeft_first T U)

private theorem lastVertex_wedge (T U : NCode) :
    pointAt U (ULift.up (Fin.last U.len)) ≫ wedgeιRight T U =
      SSet.yonedaEquiv.symm (wedge T U).last := by
  apply SSet.yonedaEquiv.injective
  simpa only [SSet.yonedaEquiv_comp, pointAt_vertex,
    Equiv.apply_symm_apply, last] using (wedgeιRight_last T U)

theorem glue_first (W : Source) (T U : NCode) (k : SimplexCategory)
    (a : K k ⟶ labels W T) (b : K k ⟶ labels W U)
    (h : a ≫ lastRestriction W T = b ≫ firstRestriction W U) :
    glue W T U k a b h ≫ firstRestriction W (wedge T U) =
      a ≫ firstRestriction W T := by
  have hp : firstRestriction W (wedge T U) =
      diagramMappingPrecomp (F.map (wedgeιLeft T U)) W ≫
        firstRestriction W T := by
    rw [firstRestriction, firstRestriction, ← diagramMappingPrecomp_comp,
      ← Functor.map_comp, firstVertex_wedge]
    rfl
  rw [hp, ← Category.assoc, glue_left]

theorem glue_last (W : Source) (T U : NCode) (k : SimplexCategory)
    (a : K k ⟶ labels W T) (b : K k ⟶ labels W U)
    (h : a ≫ lastRestriction W T = b ≫ firstRestriction W U) :
    glue W T U k a b h ≫ lastRestriction W (wedge T U) =
      b ≫ lastRestriction W U := by
  have hp : lastRestriction W (wedge T U) =
      diagramMappingPrecomp (F.map (wedgeιRight T U)) W ≫
        lastRestriction W U := by
    rw [lastRestriction, lastRestriction, ← diagramMappingPrecomp_comp,
      ← Functor.map_comp, lastVertex_wedge]
    rfl
  rw [hp, ← Category.assoc, glue_right]

/-- Complete input families, both joint equalities, and the unchanged
original outer zero-row vertices, at an arbitrary inner degree. -/
structure Families (W : Source) (d : ℕ) (k : SimplexCategory)
    (x y : (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)) where
  left : K k ⟶ labels W (single 1)
  middle : K k ⟶ labels W (single d)
  right : K k ⟶ labels W (single 1)
  leftJoint : left ≫ lastRestriction W (single 1) =
    middle ≫ firstRestriction W (single d)
  rightJoint : middle ≫ lastRestriction W (single d) =
    right ≫ firstRestriction W (single 1)
  firstOuter : left ≫ firstRestriction W (single 1) =
    SSet.stdSimplex.isTerminalObj₀.from (K k) ≫
      OrderedNecklaceVertexPoints.zeroPoint W x
  lastOuter : right ≫ lastRestriction W (single 1) =
    SSet.stdSimplex.isTerminalObj₀.from (K k) ≫
      OrderedNecklaceVertexPoints.zeroPoint W y

variable {W : Source} {d : ℕ} {k : SimplexCategory}
variable {x y : (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)}

def innerLabel (a : Families W d k x y) :
    K k ⟶ labels W (wedge (single d) (single 1)) :=
  glue W (single d) (single 1) k a.middle a.right a.rightJoint

/-- The second gluing condition is inherited from the first native joint. -/
private theorem outerJoint (a : Families W d k x y) :
    a.left ≫ lastRestriction W (single 1) =
      innerLabel a ≫ firstRestriction W (wedge (single d) (single 1)) := by
  calc
    _ = a.middle ≫ firstRestriction W (single d) := a.leftJoint
    _ = innerLabel a ≫ firstRestriction W (wedge (single d) (single 1)) :=
      (glue_first W (single d) (single 1) k
        a.middle a.right a.rightJoint).symm

def tripleLabel (a : Families W d k x y) : K k ⟶ labels W (code d) :=
  glue W (single 1) (wedge (single d) (single 1)) k a.left
    (innerLabel a) (outerJoint a)

/-- Each complete family is recovered along its ACTUAL native bead map. -/
theorem tripleLabel_left (a : Families W d k x y) :
    tripleLabel a ≫ diagramMappingPrecomp
      (F.map (tripleRightT (single 1) (single d) (single 1))) W = a.left :=
  glue_left W (single 1) (wedge (single d) (single 1)) k
    a.left (innerLabel a) (outerJoint a)

theorem tripleLabel_middle (a : Families W d k x y) :
    tripleLabel a ≫ diagramMappingPrecomp
      (F.map (tripleRightU (single 1) (single d) (single 1))) W = a.middle := by
  have hp : diagramMappingPrecomp
      (F.map (tripleRightU (single 1) (single d) (single 1))) W =
      diagramMappingPrecomp
        (F.map (wedgeιRight (single 1) (wedge (single d) (single 1)))) W ≫
      diagramMappingPrecomp (F.map (wedgeιLeft (single d) (single 1))) W := by
    dsimp only [tripleRightU]
    rw [Functor.map_comp, diagramMappingPrecomp_comp]
  rw [hp, ← Category.assoc]
  rw [show tripleLabel a ≫ diagramMappingPrecomp
      (F.map (wedgeιRight (single 1) (wedge (single d) (single 1)))) W =
        innerLabel a from glue_right W _ _ k a.left (innerLabel a) (outerJoint a)]
  exact glue_left W (single d) (single 1) k a.middle a.right a.rightJoint

theorem tripleLabel_right (a : Families W d k x y) :
    tripleLabel a ≫ diagramMappingPrecomp
      (F.map (tripleRightV (single 1) (single d) (single 1))) W = a.right := by
  have hp : diagramMappingPrecomp
      (F.map (tripleRightV (single 1) (single d) (single 1))) W =
      diagramMappingPrecomp
        (F.map (wedgeιRight (single 1) (wedge (single d) (single 1)))) W ≫
      diagramMappingPrecomp (F.map (wedgeιRight (single d) (single 1))) W := by
    dsimp only [tripleRightV]
    rw [Functor.map_comp, diagramMappingPrecomp_comp]
  rw [hp, ← Category.assoc]
  rw [show tripleLabel a ≫ diagramMappingPrecomp
      (F.map (wedgeιRight (single 1) (wedge (single d) (single 1)))) W =
        innerLabel a from glue_right W _ _ k a.left (innerLabel a) (outerJoint a)]
  exact glue_right W (single d) (single 1) k a.middle a.right a.rightJoint

theorem tripleLabel_first (a : Families W d k x y) :
    tripleLabel a ≫ firstRestriction W (code d) =
      a.left ≫ firstRestriction W (single 1) :=
  glue_first W (single 1) (wedge (single d) (single 1)) k
    a.left (innerLabel a) (outerJoint a)

theorem tripleLabel_last (a : Families W d k x y) :
    tripleLabel a ≫ lastRestriction W (code d) =
      a.right ≫ lastRestriction W (single 1) := by
  calc
    _ = innerLabel a ≫ lastRestriction W (wedge (single d) (single 1)) :=
      glue_last W (single 1) (wedge (single d) (single 1)) k
        a.left (innerLabel a) (outerJoint a)
    _ = _ := glue_last W (single d) (single 1) k
      a.middle a.right a.rightJoint

private theorem boundary_first (W : Source) (T : NCode) :
    (necklaceBoundaryRestriction W).app (op T) ≫
      diagramMappingPrecomp
        (coprod.inl : F.obj (Δ[0] : SSet.{0}) ⟶ boundary) W =
      firstRestriction W T := by
  change diagramMappingPrecomp (boundaryNecklace T) W ≫
    diagramMappingPrecomp coprod.inl W = _
  rw [← diagramMappingPrecomp_comp]
  simp only [boundaryNecklace, coprod.inl_desc, firstRestriction]
  rfl

private theorem boundary_last (W : Source) (T : NCode) :
    (necklaceBoundaryRestriction W).app (op T) ≫
      diagramMappingPrecomp
        (coprod.inr : F.obj (Δ[0] : SSet.{0}) ⟶ boundary) W =
      lastRestriction W T := by
  change diagramMappingPrecomp (boundaryNecklace T) W ≫
    diagramMappingPrecomp coprod.inr W = _
  rw [← diagramMappingPrecomp_comp]
  simp only [boundaryNecklace, coprod.inr_desc, lastRestriction]
  rfl

/-- The two outer equations imply the whole original ordered boundary,
not just the degree-zero endpoint pair. -/
theorem tripleLabel_boundary (a : Families W d k x y) :
    tripleLabel a ≫ (necklaceBoundaryRestriction W).app (op (code d)) =
      SSet.stdSimplex.isTerminalObj₀.from (K k) ≫
        OrderedNecklaceVertexPoints.boundaryPoint W x y := by
  apply (cancel_mono (OrderedNecklaceVertexPoints.boundaryMappingIso W).hom).mp
  apply prod.hom_ext
  · simp only [Category.assoc,
      OrderedNecklaceVertexPoints.boundaryMappingIso_fst]
    rw [boundary_first]
    rw [tripleLabel_first, a.firstOuter]
    rw [OrderedNecklaceVertexPoints.boundaryPoint_first]
  · simp only [Category.assoc,
      OrderedNecklaceVertexPoints.boundaryMappingIso_snd]
    rw [boundary_last]
    rw [tripleLabel_last, a.lastOuter]
    rw [OrderedNecklaceVertexPoints.boundaryPoint_last]

/-- The literal degree-`k` element of the original ordered pullback. -/
def orderedPoint (a : Families W d k x y) :
    ((orderedNecklaceLabels W
      (OrderedNecklaceVertexPoints.boundaryPoint W x y)).obj
        (op (code d))).obj (op k) :=
  SSet.yonedaEquiv (pullback.lift (tripleLabel a)
    (SSet.stdSimplex.isTerminalObj₀.from (K k)) (tripleLabel_boundary a))

/-- Its actual first projection is the COMPLETE glued family. -/
theorem orderedPoint_coefficient (a : Families W d k x y) :
    JTRealizedLabelEndpoints.orderedLabel W x y (code d) k (orderedPoint a) =
      SSet.yonedaEquiv (tripleLabel a) := by
  dsimp only [JTRealizedLabelEndpoints.orderedLabel, orderedPoint]
  erw [← SSet.yonedaEquiv_comp, pullback.lift_fst]
  rfl

/-- All three complete restrictions survive passage through the ordered
pullback projection. -/
theorem orderedPoint_left (a : Families W d k x y) :
    SSet.yonedaEquiv.symm
        (JTRealizedLabelEndpoints.orderedLabel W x y (code d) k (orderedPoint a)) ≫
      diagramMappingPrecomp
        (F.map (tripleRightT (single 1) (single d) (single 1))) W = a.left := by
  rw [orderedPoint_coefficient]
  erw [Equiv.symm_apply_apply]
  exact tripleLabel_left a

theorem orderedPoint_middle (a : Families W d k x y) :
    SSet.yonedaEquiv.symm
        (JTRealizedLabelEndpoints.orderedLabel W x y (code d) k (orderedPoint a)) ≫
      diagramMappingPrecomp
        (F.map (tripleRightU (single 1) (single d) (single 1))) W = a.middle := by
  rw [orderedPoint_coefficient]
  erw [Equiv.symm_apply_apply]
  exact tripleLabel_middle a

theorem orderedPoint_right (a : Families W d k x y) :
    SSet.yonedaEquiv.symm
        (JTRealizedLabelEndpoints.orderedLabel W x y (code d) k (orderedPoint a)) ≫
      diagramMappingPrecomp
        (F.map (tripleRightV (single 1) (single d) (single 1))) W = a.right := by
  rw [orderedPoint_coefficient]
  erw [Equiv.symm_apply_apply]
  exact tripleLabel_right a

/-- The same three equations in the literal coefficient type used by
`JTNecklaceLabelRealization.realizedLabel_natural_X`. -/
theorem orderedPoint_left_coefficient (a : Families W d k x y) :
    Functor.whiskerRight
        (F.map (tripleRightT (single 1) (single d) (single 1)))
        (tensorRight (K k)) ≫
      JTRealizedLabelEndpoints.orderedLabel W x y (code d) k (orderedPoint a) =
        SSet.yonedaEquiv a.left := by
  have h := congrArg SSet.yonedaEquiv (orderedPoint_left a)
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at h
  exact h

theorem orderedPoint_middle_coefficient (a : Families W d k x y) :
    Functor.whiskerRight
        (F.map (tripleRightU (single 1) (single d) (single 1)))
        (tensorRight (K k)) ≫
      JTRealizedLabelEndpoints.orderedLabel W x y (code d) k (orderedPoint a) =
        SSet.yonedaEquiv a.middle := by
  have h := congrArg SSet.yonedaEquiv (orderedPoint_middle a)
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at h
  exact h

theorem orderedPoint_right_coefficient (a : Families W d k x y) :
    Functor.whiskerRight
        (F.map (tripleRightV (single 1) (single d) (single 1)))
        (tensorRight (K k)) ≫
      JTRealizedLabelEndpoints.orderedLabel W x y (code d) k (orderedPoint a) =
        SSet.yonedaEquiv a.right := by
  have h := congrArg SSet.yonedaEquiv (orderedPoint_right a)
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at h
  exact h

end

end DaggerModels.PartII.TripleBeadEndpointLabel
