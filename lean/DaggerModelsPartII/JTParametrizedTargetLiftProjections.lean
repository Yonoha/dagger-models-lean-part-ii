import DaggerModelsPartII.JTParametrizedTargetFamilies

/-!
Expose both projections of a full parameter-family lift before substituting
large concrete graph families. These are the original pullback projections;
no new square, raw equation, source, time or collapse is assumed.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTParametrizedTargetLiftProjections

open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTParametrizedTargetFamilies (Family codes liftNatural)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ OrderedLabelElements.Index W (boundaryPoint W x y)}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time) (a : A)

/-- The first leg is the graph of the entire original parameter. -/
theorem decorated :
    (liftNatural F).app a ≫ JTTargetCommaPullback.fst W x y Q (L.obj a) =
      JTParametrizedTargetLiftTransport.graph (F.parameter a) :=
  JTCylinderOverTarget.lift_decorated W x y Q (L.obj a) ((codes L).obj a)
    (time.obj a) (JTParametrizedTargetLiftTransport.graph (F.parameter a))
    (F.collapse.app a) (F.raw a)

/-- The second leg is the whole native cylinder followed by its collapse. -/
theorem native :
    (liftNatural F).app a ≫ JTTargetCommaPullback.snd W x y Q (L.obj a) =
      JTCylinderOverTarget.native W x y Q ((codes L).obj a) (time.obj a)
        (F.collapse.app a) :=
  JTCylinderOverTarget.lift_native W x y Q (L.obj a) ((codes L).obj a)
    (time.obj a) (JTParametrizedTargetLiftTransport.graph (F.parameter a))
    (F.collapse.app a) (F.raw a)

end
end DaggerModels.PartII.JTParametrizedTargetLiftProjections
