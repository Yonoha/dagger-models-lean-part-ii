import DaggerModelsPartII.JTDecoratedIntervalEndpoint

/-! Restriction of endpoint-fixed lifts along the actual maps of source necklaces. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTDecoratedIntervalSourceRestriction

open NecklaceCode JTTargetJointMarks
open JTDecoratedCylinderOverMapping (rawMapping rawTarget rawPrecomp rawPostcomp)
open JTDecoratedIntervalEndpoint
open JTDecoratedIntervalMapping (toLeft toRight leftToOverlap rightToOverlap)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable (W : Source) (x y : Vertex W)
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (K : SimplexCategory ⥤ SSet.{0})


/-- Restriction of a full map preserves the specified endpoint value. -/
theorem fixedAt_precomp {P P' : Over Q.code.toSSet} (g : P ⟶ P')
    (i : DecoratedNecklaceHomDiagram.Index W x y)
    (p : Δ[0] ⟶ P.left) (p' : Δ[0] ⟶ P'.left)
    (h : p ≫ g.left = p') (e : Δ[0] ⟶ ((rawTarget W x y).obj i).left) :
    fixedAt W x y Q K P' i p' e ≤
      (fixedAt W x y Q K P i p e).preimage (rawPrecomp W x y Q K g i) := by
  intro k m hm
  change (p' ⊗ₘ 𝟙 (K.obj k.unop)) ≫ m.left =
    fst (Δ[0] : SSet.{0}) (K.obj k.unop) ≫ e at hm
  change (p ⊗ₘ 𝟙 (K.obj k.unop)) ≫ ((g.left ⊗ₘ 𝟙 (K.obj k.unop)) ≫ m.left) =
    fst (Δ[0] : SSet.{0}) (K.obj k.unop) ≫ e
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, h]
  exact hm

open JTTargetIntervalOverMapping (whole left right leftToWhole rightToWhole left_first right_last)
open JTDecoratedIntervalMapping (firstLeft lastRight cylinderFirst cylinderLast)

variable {P P' : Over Q.code} (g : P ⟶ P') (j : Joint Q.code)

private theorem whole_first :
    pointAt P.left (ULift.up 0) ≫ ((whole Q.code).map g).left =
      pointAt P'.left (ULift.up 0) := by
  rw [pointAt_comp]
  exact congrArg (pointAt P'.left) (ULift.ext _ _ (orderMap_first g.left))

private theorem whole_last :
    pointAt P.left (ULift.up (Fin.last P.left.len)) ≫ ((whole Q.code).map g).left =
      pointAt P'.left (ULift.up (Fin.last P'.left.len)) := by
  rw [pointAt_comp]
  exact congrArg (pointAt P'.left) (ULift.ext _ _ (orderMap_last g.left))

private theorem left_endpoint :
    firstLeft P j ≫ ((left Q.code j).map g).left = firstLeft P' j := by
  have h := congrArg CommaMorphism.left ((leftToWhole Q.code j).naturality g)
  let ι := ((leftToWhole Q.code j).app P').left
  haveI : Mono ι := by
    unfold ι
    change Mono (JTTargetIntervalGluing.leftInclusion P'.hom j)
    unfold JTTargetIntervalGluing.leftInclusion JTTargetIntervalPullback.sourceInclusion
    infer_instance
  apply (cancel_mono ι).mp
  change (firstLeft P j ≫ ((left Q.code j).map g).left) ≫
      ((leftToWhole Q.code j).app P').left =
    firstLeft P' j ≫ ((leftToWhole Q.code j).app P').left
  change ((left Q.code j).map g).left ≫ ((leftToWhole Q.code j).app P').left =
    ((leftToWhole Q.code j).app P).left ≫ ((whole Q.code).map g).left at h
  have hp : firstLeft P j ≫ ((leftToWhole Q.code j).app P).left =
      pointAt P.left (ULift.up 0) := left_first Q.code j P
  have hp' : firstLeft P' j ≫ ((leftToWhole Q.code j).app P').left =
      pointAt P'.left (ULift.up 0) := left_first Q.code j P'
  rw [Category.assoc, h, ← Category.assoc, hp, hp', whole_first W x y Q g]

private theorem right_endpoint :
    lastRight P j ≫ ((right Q.code j).map g).left = lastRight P' j := by
  have h := congrArg CommaMorphism.left ((rightToWhole Q.code j).naturality g)
  let ι := ((rightToWhole Q.code j).app P').left
  haveI : Mono ι := by
    unfold ι
    change Mono (JTTargetIntervalGluing.rightInclusion P'.hom j)
    unfold JTTargetIntervalGluing.rightInclusion JTTargetIntervalPullback.sourceInclusion
    infer_instance
  apply (cancel_mono ι).mp
  change (lastRight P j ≫ ((right Q.code j).map g).left) ≫
      ((rightToWhole Q.code j).app P').left =
    lastRight P' j ≫ ((rightToWhole Q.code j).app P').left
  change ((right Q.code j).map g).left ≫ ((rightToWhole Q.code j).app P').left =
    ((rightToWhole Q.code j).app P).left ≫ ((whole Q.code).map g).left at h
  have hp : lastRight P j ≫ ((rightToWhole Q.code j).app P).left =
      pointAt P.left (ULift.up (Fin.last P.left.len)) := right_last Q.code j P
  have hp' : lastRight P' j ≫ ((rightToWhole Q.code j).app P').left =
      pointAt P'.left (ULift.up (Fin.last P'.left.len)) := right_last Q.code j P'
  rw [Category.assoc, h, ← Category.assoc, hp, hp', whole_last W x y Q g]

private theorem raw_pre_comp {A B C : Over Q.code.toSSet} (f : A ⟶ B) (k : B ⟶ C)
    (i : DecoratedNecklaceHomDiagram.Index W x y) :
    rawPrecomp W x y Q K k i ≫ rawPrecomp W x y Q K f i =
      rawPrecomp W x y Q K (f ≫ k) i := by
  apply NatTrans.ext
  funext n m
  let frame := JTOverParametrizedMapping.frame K Q.code.toSSet
  let post := Over.map Q.map
  change post.map ((frame.map f).app n.unop) ≫
      post.map ((frame.map k).app n.unop) ≫ m =
    post.map ((frame.map (f ≫ k)).app n.unop) ≫ m
  rw [← Category.assoc, ← post.map_comp, frame.map_comp, NatTrans.comp_app]

variable (i : DecoratedNecklaceHomDiagram.Index W x y)

/-- Restrict the first-endpoint lift along the entire left interval. -/
def restrictLeft : (leftFixed W x y Q K P' j i).toSSet ⟶
    (leftFixed W x y Q K P j i).toSSet :=
  SSet.Subcomplex.homOfLE
      (fixedAt_precomp W x y Q K ((left Q.code j).map g) i
        (firstLeft P j) (firstLeft P' j) (left_endpoint W x y Q g j) (cylinderFirst W x y i)) ≫
    (leftFixed W x y Q K P j i).fromPreimage (rawPrecomp W x y Q K ((left Q.code j).map g) i)

/-- Restrict the last-endpoint lift along the entire right interval. -/
def restrictRight : (rightFixed W x y Q K P' j i).toSSet ⟶
    (rightFixed W x y Q K P j i).toSSet :=
  SSet.Subcomplex.homOfLE
      (fixedAt_precomp W x y Q K ((right Q.code j).map g) i
        (lastRight P j) (lastRight P' j) (right_endpoint W x y Q g j) (cylinderLast W x y i)) ≫
    (rightFixed W x y Q K P j i).fromPreimage (rawPrecomp W x y Q K ((right Q.code j).map g) i)

private theorem raw_left :
    toLeft W x y Q K P' j i ≫ rawPrecomp W x y Q K ((left Q.code j).map g) i =
      rawPrecomp W x y Q K ((whole Q.code).map g) i ≫ toLeft W x y Q K P j i := by
  change rawPrecomp W x y Q K ((leftToWhole Q.code j).app P') i ≫
      rawPrecomp W x y Q K ((left Q.code j).map g) i =
    rawPrecomp W x y Q K ((whole Q.code).map g) i ≫
      rawPrecomp W x y Q K ((leftToWhole Q.code j).app P) i
  rw [raw_pre_comp, raw_pre_comp, (leftToWhole Q.code j).naturality g]

private theorem raw_right :
    toRight W x y Q K P' j i ≫ rawPrecomp W x y Q K ((right Q.code j).map g) i =
      rawPrecomp W x y Q K ((whole Q.code).map g) i ≫ toRight W x y Q K P j i := by
  change rawPrecomp W x y Q K ((rightToWhole Q.code j).app P') i ≫
      rawPrecomp W x y Q K ((right Q.code j).map g) i =
    rawPrecomp W x y Q K ((whole Q.code).map g) i ≫
      rawPrecomp W x y Q K ((rightToWhole Q.code j).app P) i
  rw [raw_pre_comp, raw_pre_comp, (rightToWhole Q.code j).naturality g]

private theorem wholeFixed_precomp :
    wholeFixed W x y Q K P' j i ≤
      (wholeFixed W x y Q K P j i).preimage (rawPrecomp W x y Q K ((whole Q.code).map g) i) := by
  intro k m hm
  change (toLeft W x y Q K P' j i).app k m ∈ (leftFixed W x y Q K P' j i).obj k ∧
    (toRight W x y Q K P' j i).app k m ∈ (rightFixed W x y Q K P' j i).obj k at hm
  let n := (rawPrecomp W x y Q K ((whole Q.code).map g) i).app k m
  change (toLeft W x y Q K P j i).app k n ∈ (leftFixed W x y Q K P j i).obj k ∧
    (toRight W x y Q K P j i).app k n ∈ (rightFixed W x y Q K P j i).obj k
  have hL := congrFun (NatTrans.congr_app (raw_left W x y Q K g j i) k) m
  have hR := congrFun (NatTrans.congr_app (raw_right W x y Q K g j i) k) m
  have h₁ := fixedAt_precomp W x y Q K ((left Q.code j).map g) i
    (firstLeft P j) (firstLeft P' j) (left_endpoint W x y Q g j) (cylinderFirst W x y i) k hm.1
  have h₂ := fixedAt_precomp W x y Q K ((right Q.code j).map g) i
    (lastRight P j) (lastRight P' j) (right_endpoint W x y Q g j) (cylinderLast W x y i) k hm.2
  exact ⟨hL ▸ h₁, hR ▸ h₂⟩

/-- Restrict the whole lift along a native source map, keeping both endpoints. -/
def restrictWhole : (wholeFixed W x y Q K P' j i).toSSet ⟶
    (wholeFixed W x y Q K P j i).toSSet :=
  SSet.Subcomplex.homOfLE (wholeFixed_precomp W x y Q K g j i) ≫
    (wholeFixed W x y Q K P j i).fromPreimage (rawPrecomp W x y Q K ((whole Q.code).map g) i)

/-- Restricting a native source commutes with taking its left interval. -/
theorem left_square :
    toLeftFixed W x y Q K P' j i ≫ restrictLeft W x y Q K g j i =
      restrictWhole W x y Q K g j i ≫ toLeftFixed W x y Q K P j i := by
  apply NatTrans.ext
  funext k m
  exact Subtype.ext (congrFun (NatTrans.congr_app (raw_left W x y Q K g j i) k) m.val)

/-- Restricting a native source commutes with taking its right interval. -/
theorem right_square :
    toRightFixed W x y Q K P' j i ≫ restrictRight W x y Q K g j i =
      restrictWhole W x y Q K g j i ≫ toRightFixed W x y Q K P j i := by
  apply NatTrans.ext
  funext k m
  exact Subtype.ext (congrFun (NatTrans.congr_app (raw_right W x y Q K g j i) k) m.val)

end
end DaggerModels.PartII.JTDecoratedIntervalSourceRestriction
