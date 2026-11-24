import DaggerModelsPartII.JTActualJointChoicePrism
import DaggerModelsPartII.JTFullPrismSupport

/-! Lifted endpoint parameters retain the relative identity face on ordered chains. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTActualJointChainEndpointSupport

open JTParametrizedTargetFamilies (Family)
open JTTargetJointMarks (Joint)
open JTActualJointChoiceCover (Cover projection)
open JTActualJointChoicePrism (coefficient choiceTime ending starting)
open JTExactlyMarkedSourceDiagram (supports incl)
open JTActualSourceJointSupport (liftedOverlapVertex timeParameter timeParameter_factor)
open JTJointTimedEndpointSupport (timedParameter supportedTimedParameter_fac)
open JTPrismRectangle (sample supportMap supportMap_inclusion)
open JTRowGraphParameterSupport (supportOrdinal inclusion)
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev J := GroupoidSimplex.parameter

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code) (c : Cover F j)

private abbrev a := (projection F j).obj c
private abbrev z := JTParametrizedBeadGraph.jointCoefficient (Q := Q) j

/-- The whole original endpoint prism at the actual exactly marked cut. -/
abbrev oldEndpoint :=
  timedParameter F (a F j c).1 j
    (liftedOverlapVertex F (a F j c).1 j (a F j c).2.val (a F j c).2.property)

/-- This is the original Family parameter restricted to the named source vertex. -/
theorem oldEndpoint_eq :
    oldEndpoint F j c = timeParameter F (a F j c).1 (a F j c).2.val :=
  (supportedTimedParameter_fac F (a F j c).1 j
    (liftedOverlapVertex F (a F j c).1 j (a F j c).2.val (a F j c).2.property)).symm.trans
      (timeParameter_factor F (a F j c).1 j (a F j c).2.val (a F j c).2.property)

variable {d r t : SimplexCategory}
variable (α : d ⟶ (coefficient F j).obj c) (β : d ⟶ (choiceTime F j).obj c)
variable (q : std.obj r ⊗ J.obj t ⟶ J.obj d)
variable (g : std.obj r ⊗ J.obj t ⟶
  (Δ[0] : SSet.{0}) ⊗ J.obj (time.obj (a F j c).1))

/-- Every used lifted coefficient maps into the old full endpoint support. -/
def supportToOriginal (h : g ≫ oldEndpoint F j c = q ≫ J.map α) :
    supportOrdinal (sample r t ≫ q) ⟶ (supports F j).obj (a F j c) :=
  supportMap q (oldEndpoint F j c) g α h

/-- The lifted used face and the old used face form the exact original ordinal square. -/
theorem supportToOriginal_inclusion (h : g ≫ oldEndpoint F j c = q ≫ J.map α) :
    supportToOriginal F j c α q g h ≫ (incl F j).app (a F j c) =
      inclusion (sample r t ≫ q) ≫ α :=
  supportMap_inclusion q (oldEndpoint F j c) g α h

/-- A lifted endpoint prism forces the ending edge to be the identity on its
entire actual support, including all original time vertices. -/
theorem ending_supported_face (h : g ≫ oldEndpoint F j c = q ≫ J.map α) :
    std.map (inclusion (sample r t ≫ q)) ≫
        lift (std.map α) (std.map β) ≫ (ending F j).app c =
      JTJointEndpointRelativeLift.identityOnFace W (z j) :=
  JTActualJointChoicePrism.ending_chain_face F j c α β
    (inclusion (sample r t ≫ q)) (supportToOriginal F j c α q g h)
    (supportToOriginal_inclusion F j c α q g h).symm

/-- The same whole lifted support makes the starting edge the identity. -/
theorem starting_supported_face (h : g ≫ oldEndpoint F j c = q ≫ J.map α) :
    std.map (inclusion (sample r t ≫ q)) ≫
        lift (std.map α) (std.map β) ≫ (starting F j).app c =
      JTJointEndpointRelativeLift.identityOnFace W (z j) :=
  JTActualJointChoicePrism.starting_chain_face F j c α β
    (inclusion (sample r t ≫ q)) (supportToOriginal F j c α q g h)
    (supportToOriginal_inclusion F j c α q g h).symm

end
end DaggerModels.PartII.JTActualJointChainEndpointSupport
