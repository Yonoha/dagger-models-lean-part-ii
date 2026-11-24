import DaggerModelsPartII.JTParametrizedTargetLiftTransport

/-! Identify the existing concrete binary lift with the mixed comparison API. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTBinaryLiftCompatibility

open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceLabelDiagram (orderedNecklaceLabels)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTRealizedLabelEndpoints (orderedLabel)
open JTOrderedLabelBinaryGlue (code)
open JTBinaryPrismRealization (collapse realizeProduct)
open JTBinaryPrismTargetLift (cylinderMap_raw index parameter targetLift)
open JTParametrizedTargetLiftTransport (graph)
open DecoratedCylinderNecklacePresentation (underCocone)
open NecklaceCylinderAugmentation (augmentation)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x z y : Vertex W} {T U : NecklaceCode}
variable {P : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W z)}
variable {Q : NecklacesOver (Raw W) (rawVertex W z) (rawVertex W y)}
variable {k l n : SimplexCategory}
variable (a : ((orderedNecklaceLabels W (boundaryPoint W x z)).obj (op T)).obj (op k))
variable (b : ((orderedNecklaceLabels W (boundaryPoint W z y)).obj (op U)).obj (op l))
variable (s : T.toSSet ⊗ J.obj n ⟶ J.obj k) (t : U.toSSet ⊗ J.obj n ⟶ J.obj l)
variable (c : T ⟶ P.code) (e : U ⟶ Q.code)
variable (hs : realizeProduct W k s (orderedLabel W x z T k a) =
  fst T.toSSet (J.obj n) ≫ c.map ≫ P.map)
variable (ht : realizeProduct W l t (orderedLabel W z y U l b) =
  fst U.toSSet (J.obj n) ≫ e.map ≫ Q.map)

include hs ht in
private theorem graph_raw :
    (graph (i := index a b) (parameter s t)).right ≫ ((underCocone W x y).app (index a b)).right =
      augmentation (code T U) n ≫ (collapse c e).map ≫ (NecklacesOver.wedge P Q).map := by
  change JTInterpolatedReducedCylinder.cylinderMap (code T U) (parameter s t) ≫
    ((underCocone W x y).app (index a b)).right = _
  rw [← JTBinaryPrismSideTransport.binaryCylinder_eq_interpolated]
  exact cylinderMap_raw a b s t c e hs ht

/-- The mixed comparison transport uses precisely the original
binary comparison, including its fixed raw target. -/
theorem targetLift_eq :
    targetLift a b s t c e hs ht =
      JTCylinderOverTarget.lift W x y (NecklacesOver.wedge P Q) (index a b) (code T U) n
        (graph (i := index a b) (parameter s t)) (collapse c e) (graph_raw a b s t c e hs ht) := by
  rfl

end

end DaggerModels.PartII.JTBinaryLiftCompatibility
