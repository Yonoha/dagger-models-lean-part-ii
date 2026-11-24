import DaggerModelsPartII.JTDecoratedIntervalTransport
import DaggerModelsPartII.JTDecoratedIntervalSourceRestriction

/-! The two operators on endpoint-fixed lifts commute in the original slice. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTDecoratedIntervalMixedTransport

open NecklaceCode JTTargetJointMarks
open JTDecoratedCylinderOverMapping (rawPrecomp rawPostcomp)
open JTDecoratedIntervalEndpoint
open JTDecoratedIntervalSourceRestriction
open JTDecoratedIntervalTransport


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


open JTTargetIntervalOverMapping (whole left right)

variable {P P' : Over Q.code} (g : P ⟶ P') (j : Joint Q.code)
variable {i i' : DecoratedNecklaceHomDiagram.Index W x y} (u : i ⟶ i')

/-- On full lifts, native restriction commutes with the decorated operator. -/
theorem whole_comm :
    restrictWhole W x y Q K g j i ≫ mapWhole W x y Q K P j u =
      mapWhole W x y Q K P' j u ≫ restrictWhole W x y Q K g j i' := by
  apply NatTrans.ext
  funext k m
  exact Subtype.ext (congrFun (NatTrans.congr_app
    (raw_pre_post W x y Q K ((whole Q.code).map g) u) k) m.val)

/-- On left lifts, native restriction commutes with the decorated operator. -/
theorem left_comm :
    restrictLeft W x y Q K g j i ≫ mapLeft W x y Q K P j u =
      mapLeft W x y Q K P' j u ≫ restrictLeft W x y Q K g j i' := by
  apply NatTrans.ext
  funext k m
  exact Subtype.ext (congrFun (NatTrans.congr_app
    (raw_pre_post W x y Q K ((left Q.code j).map g) u) k) m.val)

/-- On right lifts, native restriction commutes with the decorated operator. -/
theorem right_comm :
    restrictRight W x y Q K g j i ≫ mapRight W x y Q K P j u =
      mapRight W x y Q K P' j u ≫ restrictRight W x y Q K g j i' := by
  apply NatTrans.ext
  funext k m
  exact Subtype.ext (congrFun (NatTrans.congr_app
    (raw_pre_post W x y Q K ((right Q.code j).map g) u) k) m.val)

end
end DaggerModels.PartII.JTDecoratedIntervalMixedTransport
