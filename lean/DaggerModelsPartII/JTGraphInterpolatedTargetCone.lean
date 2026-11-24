import DaggerModelsPartII.JTGraphInterpolatedTargetOperators
import DaggerModelsPartII.JTGraphInterpolatedOverOriginal
import DaggerModelsPartII.JTBoundaryNecklaceConeTriangle

/-! The target-transport triangle in the original pullback presentation. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphInterpolatedTargetCone

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphLiftTransport (GraphLift)
open JTGraphInterpolatedComparison (Fiber)
open JTGraphInterpolatedCollapseOriginal (indexCollapse timeCollapse)
open JTGraphInterpolatedOverOriginal (presentationCone)
open JTGraphInterpolatedTransport (indexArrow transportPresentation)
open JTGraphInterpolatedTargetOperators (transported_collapse indexCollapse_transport
  timeCollapse_transport)
open JTCylinderOverTargetBaseChange (comparisonOfSquare_base comparisonOfSquare_code)
open JTNecklaceEndpointCylinder (under)
open JTTargetCommaPullback (diagram toPullback)
open BoundaryNecklaceComma (necklaceUnder)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {U V : TargetComma Q} {S : NecklaceCode} {n : SimplexCategory}
variable (c : S ⟶ U.left.fiber.left)
variable (D : Fin (n.len + 1) → GraphLift U.left S)
variable (hD : ∀ i, (D i).collapse = c)
variable (a : U ⟶ V)

private abbrev transported (i : Fin (n.len + 1)) : GraphLift V.left S := (D i).transport a.left

private abbrev transportedCode : S ⟶ V.left.fiber.left := c ≫ a.left.fiber.left

include hD in
private theorem transportedCollapse (i : Fin (n.len + 1)) :
    (transported D a i).collapse = transportedCode c a :=
  transported_collapse c D hD a i

private abbrev time := (under S).obj n

private abbrev timeMap : Fiber S n ⥤ Fiber S n :=
  CostructuredArrow.map (S := necklaceUnder) (𝟙 (time (S := S) (n := n)))

private abbrev U' := (toPullback W x y Q).obj U

private abbrev V' := (toPullback W x y Q).obj V

/-- The original cone in the fixed-target pullback. -/
def sourceCone := presentationCone (n := n) c D hD

/-- The original cone on the transported family. -/
def targetCone :=
  presentationCone (n := n) (transportedCode c a) (transported D a)
    (transportedCollapse c D hD a)

private def arrow : (U' (U := U)) ⟶ (V' (V := V)) := (toPullback W x y Q).map a

private def presentationTransport := transportPresentation c D hD a

set_option maxHeartbeats 65000 in
private theorem transportPresentation_base (P : Fiber S n) :
    ((presentationTransport c D hD a).app P).base = indexArrow c D hD a := by
  unfold presentationTransport
  exact comparisonOfSquare_base _ _ _ _ _ _ _

set_option maxHeartbeats 65000 in
private theorem transportPresentation_code (P : Fiber S n) :
    (BoundaryNecklaceComma.sourceCode (diagram W x y Q)).map
      ((presentationTransport c D hD a).app P) = 𝟙 P.left := by
  unfold presentationTransport
  exact comparisonOfSquare_code _ _ _ _ _ _ _

set_option maxHeartbeats 65000 in
private theorem transport_triangle_base (P : Fiber S n) :
    (((presentationTransport c D hD a).app P) ≫
        (targetCone c D hD a).app (timeMap.obj P)).base =
      ((sourceCone c D hD).app P ≫ arrow a).base := by
  change ((presentationTransport c D hD a).app P).base ≫
      indexCollapse (transportedCode c a) (transported D a) (transportedCollapse c D hD a) =
    indexCollapse c D hD ≫ (arrow a).base
  rw [transportPresentation_base]
  exact indexCollapse_transport c D hD a

private theorem time_native_triangle (P : Fiber S n) :
    ((P.hom ≫ 𝟙 ((under S).obj n)) ≫ timeCollapse (n := n) (transportedCode c a)).right =
      (P.hom ≫ timeCollapse (n := n) c).right ≫ (arrow a).fiber.left.map := by
  change _ = ((P.hom ≫ timeCollapse (n := n) c) ≫
    necklaceUnder.map (arrow a).fiber.left).right
  rw [Category.assoc]
  exact (congrArg
    (fun v : (under S).obj n ⟶ necklaceUnder.obj V.left.fiber.left ↦ (P.hom ≫ v).right)
    (timeCollapse_transport (n := n) c a)).trans (congrArg
      (fun v : necklaceUnder.obj P.left ⟶ necklaceUnder.obj V.left.fiber.left ↦ v.right)
      (Category.assoc P.hom (timeCollapse (n := n) c)
        (necklaceUnder.map (arrow a).fiber.left)).symm)

set_option maxHeartbeats 180000 in
private theorem transport_triangle_code (P : Fiber S n) :
    (BoundaryNecklaceComma.sourceCode (diagram W x y Q)).map
      (((presentationTransport c D hD a).app P) ≫
        (targetCone c D hD a).app (timeMap.obj P)) =
      (BoundaryNecklaceComma.sourceCode (diagram W x y Q)).map
        ((sourceCone c D hD).app P ≫ arrow a) := by
  rw [Functor.map_comp, Functor.map_comp, transportPresentation_code]
  refine (Category.id_comp _).trans ?_
  apply NecklaceCode.Hom.ext
  change ((P.hom ≫ 𝟙 ((under S).obj n)) ≫ timeCollapse (n := n) (transportedCode c a)).right =
    (P.hom ≫ timeCollapse (n := n) c).right ≫ (arrow a).fiber.left.map
  exact time_native_triangle c a P

set_option maxHeartbeats 100000 in
private theorem presentation_transport_triangle_internal :
    presentationTransport c D hD a ≫ Functor.whiskerLeft timeMap (targetCone c D hD a) =
      sourceCone c D hD ≫ (Functor.const (Fiber S n)).map (arrow a) := by
  ext : 1
  funext P
  exact JTTargetCommaPullback.operator_ext (transport_triangle_base c D hD a P)
    (transport_triangle_code c D hD a P)

set_option maxHeartbeats 100000 in
/-- Target transport preserves the original collapse cone in the pullback presentation. -/
theorem presentation_transport_triangle :
    transportPresentation c D hD a ≫ Functor.whiskerLeft timeMap (targetCone c D hD a) =
      sourceCone c D hD ≫ (Functor.const (Fiber S n)).map (arrow a) :=
  presentation_transport_triangle_internal c D hD a

end

end DaggerModels.PartII.JTGraphInterpolatedTargetCone
