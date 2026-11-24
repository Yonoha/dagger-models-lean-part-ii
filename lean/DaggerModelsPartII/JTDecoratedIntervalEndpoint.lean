import DaggerModelsPartII.JTDecoratedIntervalMapping

/-!
# The endpoint-fixed gluing of the actual cylinder lift spaces

The two outer endpoints define subcomplexes of the actual left and right
lift spaces. The entire endpoint-fixed space is their strict pullback
over the unrestricted full overlap. The endpoint conditions are
preserved in every parameter degree and by every decorated operator.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTDecoratedIntervalEndpoint

noncomputable section

section SubcomplexPullback

variable {X L R M : SSet.{0}} {l : X ⟶ L} {r : X ⟶ R} {ml : L ⟶ M} {mr : R ⟶ M}
variable (A : L.Subcomplex) (B : R.Subcomplex)

private abbrev paired := A.preimage l ⊓ B.preimage r

private def leftRestriction : (paired A B (l := l) (r := r)).toSSet ⟶ A.toSSet :=
  SSet.Subcomplex.homOfLE inf_le_left ≫ A.fromPreimage l

private def rightRestriction : (paired A B (l := l) (r := r)).toSSet ⟶ B.toSSet :=
  SSet.Subcomplex.homOfLE inf_le_right ≫ B.fromPreimage r

private theorem subcomplex_pullback (sq : IsPullback l r ml mr) :
    IsPullback (leftRestriction A B (l := l) (r := r))
      (rightRestriction A B (l := l) (r := r)) (A.ι ≫ ml) (B.ι ≫ mr) := by
  have at_degree (k : SimplexCategoryᵒᵖ) :
      IsPullback ((leftRestriction A B (l := l) (r := r)).app k)
        ((rightRestriction A B (l := l) (r := r)).app k) ((A.ι ≫ ml).app k) ((B.ι ≫ mr).app k) := by
    have hp : IsPullback (l.app k) (r.app k) (ml.app k) (mr.app k) :=
      sq.map ((evaluation SimplexCategoryᵒᵖ (Type)).obj k)
    apply (Types.isPullback_iff _ _ _ _).mpr
    refine ⟨?_, ?_, ?_⟩
    · funext m
      exact congrFun hp.w m.val
    · intro m n h
      apply Subtype.ext
      exact Types.ext_of_isPullback hp (congrArg Subtype.val h.1) (congrArg Subtype.val h.2)
    · intro a b hab
      obtain ⟨m, hmL, hmR⟩ := Types.exists_of_isPullback hp a.val b.val hab
      have hm : m ∈ (paired A B (l := l) (r := r)).obj k := by
        change l.app k m ∈ A.obj k ∧ r.app k m ∈ B.obj k
        rw [hmL, hmR]
        exact ⟨a.property, b.property⟩
      exact ⟨⟨m, hm⟩, Subtype.ext hmL, Subtype.ext hmR⟩
  refine ⟨?_, ⟨evaluationJointlyReflectsLimits _ (fun k ↦ ?_)⟩⟩
  · constructor
    apply NatTrans.ext
    funext k m
    exact congrFun (at_degree k).w m
  · exact (PullbackCone.isLimitMapConeEquiv _ _).2 (at_degree k).isLimit

end SubcomplexPullback

open NecklaceCode JTTargetJointMarks
open JTDecoratedCylinderOverMapping (rawMapping rawTarget rawPostcomp)
open JTDecoratedIntervalMapping

local instance : SmallCategory NecklaceCode := NecklaceCode.category

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable (W : Source) (x y : Vertex W)
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (K : SimplexCategory ⥤ SSet.{0})

/-- Keep all parametrized lifts that have the fixed value on one specified endpoint. -/
def fixedAt (P : Over Q.code.toSSet) (i : DecoratedNecklaceHomDiagram.Index W x y)
    (p : Δ[0] ⟶ P.left) (e : Δ[0] ⟶ ((rawTarget W x y).obj i).left) :
    (rawMapping W x y Q K P i).Subcomplex where
  obj k := {m | (p ⊗ₘ 𝟙 (K.obj k.unop)) ≫ m.left =
    fst (Δ[0] : SSet.{0}) (K.obj k.unop) ≫ e}
  map {k l} a := by
    intro m hm
    change (p ⊗ₘ 𝟙 (K.obj k.unop)) ≫ m.left = fst (Δ[0] : SSet.{0}) (K.obj k.unop) ≫ e at hm
    change (p ⊗ₘ 𝟙 (K.obj l.unop)) ≫ ((𝟙 P.left ⊗ₘ K.map a.unop) ≫ m.left) =
      fst (Δ[0] : SSet.{0}) (K.obj l.unop) ≫ e
    have h : (p ⊗ₘ 𝟙 (K.obj l.unop)) ≫ (𝟙 P.left ⊗ₘ K.map a.unop) =
        (𝟙 (Δ[0] : SSet.{0}) ⊗ₘ K.map a.unop) ≫ (p ⊗ₘ 𝟙 (K.obj k.unop)) := by
      simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
    rw [← Category.assoc, h, Category.assoc, hm, ← Category.assoc, tensorHom_fst, Category.comp_id]

/-- Postcomposition preserves the exact endpoint equation if the target arrow
carries the designated value to the next designated value. -/
theorem fixedAt_postcomp (P : Over Q.code.toSSet) {i i' : DecoratedNecklaceHomDiagram.Index W x y}
    (u : i ⟶ i') (p : Δ[0] ⟶ P.left) {e : Δ[0] ⟶ ((rawTarget W x y).obj i).left}
    {e' : Δ[0] ⟶ ((rawTarget W x y).obj i').left}
    (he : e ≫ ((rawTarget W x y).map u).left = e') :
    fixedAt W x y Q K P i p e ≤
      (fixedAt W x y Q K P i' p e').preimage (rawPostcomp W x y Q K P u) := by
  intro k m hm
  change (p ⊗ₘ 𝟙 (K.obj k.unop)) ≫ m.left = fst (Δ[0] : SSet.{0}) (K.obj k.unop) ≫ e at hm
  change (p ⊗ₘ 𝟙 (K.obj k.unop)) ≫ (m.left ≫ ((rawTarget W x y).map u).left) =
    fst (Δ[0] : SSet.{0}) (K.obj k.unop) ≫ e'
  rw [← Category.assoc, hm, Category.assoc, he]

variable (P : Over Q.code) (j : Joint Q.code) (i : DecoratedNecklaceHomDiagram.Index W x y)

/-- Left lifts with the actual first endpoint. -/
abbrev leftFixed := fixedAt W x y Q K ((JTTargetIntervalOverMapping.left Q.code j).obj P) i
  (firstLeft P j) (cylinderFirst W x y i)

/-- Right lifts with the actual last endpoint. -/
abbrev rightFixed := fixedAt W x y Q K ((JTTargetIntervalOverMapping.right Q.code j).obj P) i
  (lastRight P j) (cylinderLast W x y i)

set_option maxHeartbeats 600000 in
/-- Every actual decorated operator preserves the fixed first endpoint on the left. -/
theorem leftFixed_postcomp {i i' : DecoratedNecklaceHomDiagram.Index W x y} (u : i ⟶ i') :
    leftFixed W x y Q K P j i ≤ (leftFixed W x y Q K P j i').preimage
      (rawPostcomp W x y Q K ((JTTargetIntervalOverMapping.left Q.code j).obj P) u) :=
  fixedAt_postcomp W x y Q K ((JTTargetIntervalOverMapping.left Q.code j).obj P)
    u (firstLeft P j) (e := cylinderFirst W x y i) (e' := cylinderFirst W x y i')
    (cylinderFirst_natural W x y u)

set_option maxHeartbeats 600000 in
/-- Every actual decorated operator preserves the fixed last endpoint on the right. -/
theorem rightFixed_postcomp {i i' : DecoratedNecklaceHomDiagram.Index W x y} (u : i ⟶ i') :
    rightFixed W x y Q K P j i ≤ (rightFixed W x y Q K P j i').preimage
      (rawPostcomp W x y Q K ((JTTargetIntervalOverMapping.right Q.code j).obj P) u) :=
  fixedAt_postcomp W x y Q K ((JTTargetIntervalOverMapping.right Q.code j).obj P)
    u (lastRight P j) (e := cylinderLast W x y i) (e' := cylinderLast W x y i')
    (cylinderLast_natural W x y u)

/-- Full lifts with both original endpoints. -/
abbrev wholeFixed :=
  (leftFixed W x y Q K P j i).preimage (toLeft W x y Q K P j i) ⊓
    (rightFixed W x y Q K P j i).preimage (toRight W x y Q K P j i)

/-- The two side conditions are exactly the original ordered endpoint conditions. -/
theorem wholeFixed_obj_iff (k : SimplexCategory)
    (m : (whole W x y Q K P i).obj (op k)) :
    m ∈ (wholeFixed W x y Q K P j i).obj (op k) ↔
      (pointAt P.left (ULift.up 0) ⊗ₘ 𝟙 (K.obj k)) ≫ m.left =
        fst (Δ[0] : SSet.{0}) (K.obj k) ≫ cylinderFirst W x y i ∧
      (pointAt P.left (ULift.up (Fin.last P.left.len)) ⊗ₘ 𝟙 (K.obj k)) ≫ m.left =
        fst (Δ[0] : SSet.{0}) (K.obj k) ≫ cylinderLast W x y i := by
  change ((firstLeft P j ⊗ₘ 𝟙 (K.obj k)) ≫ ((toLeft W x y Q K P j i).app (op k) m).left = _ ∧
    (lastRight P j ⊗ₘ 𝟙 (K.obj k)) ≫ ((toRight W x y Q K P j i).app (op k) m).left = _) ↔ _
  rw [first_restrict, last_restrict]

def toLeftFixed : (wholeFixed W x y Q K P j i).toSSet ⟶ (leftFixed W x y Q K P j i).toSSet :=
  leftRestriction (leftFixed W x y Q K P j i) (rightFixed W x y Q K P j i)
    (l := toLeft W x y Q K P j i) (r := toRight W x y Q K P j i)

def toRightFixed : (wholeFixed W x y Q K P j i).toSSet ⟶ (rightFixed W x y Q K P j i).toSSet :=
  rightRestriction (leftFixed W x y Q K P j i) (rightFixed W x y Q K P j i)
    (l := toLeft W x y Q K P j i) (r := toRight W x y Q K P j i)

/-- The endpoint-fixed cylinder lift space is the strict simplicial
pullback of the endpoint-fixed sides over the complete overlap. -/
theorem isPullback :
    IsPullback (toLeftFixed W x y Q K P j i) (toRightFixed W x y Q K P j i)
      ((leftFixed W x y Q K P j i).ι ≫ leftToOverlap W x y Q K P j i)
      ((rightFixed W x y Q K P j i).ι ≫ rightToOverlap W x y Q K P j i) :=
  subcomplex_pullback (leftFixed W x y Q K P j i) (rightFixed W x y Q K P j i)
    (JTDecoratedIntervalMapping.isPullback W x y Q K P j i)

end

end DaggerModels.PartII.JTDecoratedIntervalEndpoint
