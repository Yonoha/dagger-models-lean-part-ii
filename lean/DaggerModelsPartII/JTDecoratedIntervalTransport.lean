import DaggerModelsPartII.JTDecoratedIntervalEndpoint

/-! Transport of endpoint-fixed gluing along the actual decorated operators. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTDecoratedIntervalTransport

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

/-- Precomposition in the source and postcomposition in the decorated label commute. -/
theorem raw_pre_post {P P' : Over Q.code.toSSet} (g : P ⟶ P')
    {i i' : DecoratedNecklaceHomDiagram.Index W x y} (u : i ⟶ i') :
    rawPrecomp W x y Q K g i ≫ rawPostcomp W x y Q K P u =
      rawPostcomp W x y Q K P' u ≫ rawPrecomp W x y Q K g i' := by
  apply NatTrans.ext
  funext k m
  let source := (Over.map Q.map).map (((JTOverParametrizedMapping.frame K Q.code.toSSet).map g).app
    k.unop)
  let target := (rawTarget W x y).map u
  change (source ≫ m) ≫ target = source ≫ m ≫ target
  exact Category.assoc source m target

variable (P : Over Q.code) (j : Joint Q.code)
variable {i i' : DecoratedNecklaceHomDiagram.Index W x y} (u : i ⟶ i')

private abbrev wholeSlice (A : Over Q.code) :=
  (JTTargetIntervalOverMapping.whole Q.code).obj A

private theorem wholeFixed_postcomp :
    wholeFixed W x y Q K P j i ≤
      (wholeFixed W x y Q K P j i').preimage (rawPostcomp W x y Q K (wholeSlice W x y Q P) u) := by
  intro k m hm
  change (toLeft W x y Q K P j i).app k m ∈ (leftFixed W x y Q K P j i).obj k ∧
    (toRight W x y Q K P j i).app k m ∈ (rightFixed W x y Q K P j i).obj k at hm
  change (toLeft W x y Q K P j i').app k
      ((rawPostcomp W x y Q K (wholeSlice W x y Q P) u).app k m) ∈
      (leftFixed W x y Q K P j i').obj k ∧
    (toRight W x y Q K P j i').app k ((rawPostcomp W x y Q K (wholeSlice W x y Q P) u).app k m) ∈
      (rightFixed W x y Q K P j i').obj k
  have hl := congrFun (NatTrans.congr_app (raw_pre_post W x y Q K
    ((JTTargetIntervalOverMapping.leftToWhole Q.code j).app P) u) k) m
  have hr := congrFun (NatTrans.congr_app (raw_pre_post W x y Q K
    ((JTTargetIntervalOverMapping.rightToWhole Q.code j).app P) u) k) m
  refine ⟨?_, ?_⟩
  · exact hl ▸ leftFixed_postcomp W x y Q K P j u k hm.1
  · exact hr ▸ rightFixed_postcomp W x y Q K P j u k hm.2

private def subMap {X Y : SSet.{0}} {A : X.Subcomplex} {B : Y.Subcomplex} {f : X ⟶ Y}
    (h : A ≤ B.preimage f) : A.toSSet ⟶ B.toSSet :=
  SSet.Subcomplex.homOfLE h ≫ B.fromPreimage f

/-- Transport of the whole lift retains both original endpoints. -/
def mapWhole : (wholeFixed W x y Q K P j i).toSSet ⟶ (wholeFixed W x y Q K P j i').toSSet :=
  subMap (wholeFixed_postcomp W x y Q K P j u)

/-- Transport the left lift with the prescribed first endpoint. -/
def mapLeft : (leftFixed W x y Q K P j i).toSSet ⟶ (leftFixed W x y Q K P j i').toSSet :=
  subMap (leftFixed_postcomp W x y Q K P j u)

/-- Transport the right lift with the prescribed last endpoint. -/
def mapRight : (rightFixed W x y Q K P j i).toSSet ⟶ (rightFixed W x y Q K P j i').toSSet :=
  subMap (rightFixed_postcomp W x y Q K P j u)

/-- Transport and restriction to the complete left interval commute. -/
theorem restrict_left :
    toLeftFixed W x y Q K P j i ≫ mapLeft W x y Q K P j u =
      mapWhole W x y Q K P j u ≫ toLeftFixed W x y Q K P j i' := by
  apply NatTrans.ext
  funext k m
  apply Subtype.ext
  exact congrFun (NatTrans.congr_app (raw_pre_post W x y Q K
    ((JTTargetIntervalOverMapping.leftToWhole Q.code j).app P) u) k) m.val

/-- Transport and restriction to the complete right interval commute. -/
theorem restrict_right :
    toRightFixed W x y Q K P j i ≫ mapRight W x y Q K P j u =
      mapWhole W x y Q K P j u ≫ toRightFixed W x y Q K P j i' := by
  apply NatTrans.ext
  funext k m
  apply Subtype.ext
  exact congrFun (NatTrans.congr_app (raw_pre_post W x y Q K
    ((JTTargetIntervalOverMapping.rightToWhole Q.code j).app P) u) k) m.val

end
end DaggerModels.PartII.JTDecoratedIntervalTransport
