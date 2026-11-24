import DaggerModelsPartII.JTGraphTransportRaw
import DaggerModelsPartII.JTTargetCommaPullbackComparison

/-!
# The commuting transport square in the actual fixed-target comma
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphTransportNaturality

open JTProjectiveOrderedFiberComparison JTGraphLiftTransport
open JTGraphRestrictionRaw (predecessor)
open JTGraphTransportRaw (commaTransport)
open JTCommaGraphPredecessor (augmentationCode)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}

private abbrev F := DecoratedCylinderNecklacePresentation.toTarget W x y
variable {U V : CostructuredArrow (F (W := W) (x := x) (y := y)) Q} {S : NecklaceCode}

private abbrev baseOf := DecoratedCylinderNecklacePresentation.projection W x y ⋙
  projection (W := W) (x := x) (y := y)
private abbrev codeOf :=
  BoundaryNecklaceComma.sourceCode (DecoratedCylinderNecklacePresentation.underDiagram W x y)

/-- The original comparison from an actual graph predecessor to its presentation. -/
def toComma (D : GraphLift U.left S) : predecessor D ⟶ U :=
  JTGraphToPresentationArrow.toComma Q U S
    (D.collapse ≫ augmentationCode U.left) D.collapse D.parameter D.comm

/-- The full decorated morphisms around the transport square agree. -/
theorem commaTransport_natural (D : GraphLift U.left S) (a : U ⟶ V) :
    commaTransport D a ≫ toComma (D.transport a.left) = toComma D ≫ a := by
  apply CostructuredArrow.hom_ext
  let l := (commaTransport D a).left ≫ (toComma (D.transport a.left)).left
  let r := (toComma D).left ≫ a.left
  change l = r
  have hb : (baseOf (W := W) (x := x) (y := y)).map l =
      (baseOf (W := W) (x := x) (y := y)).map r := by
    dsimp only [l, r]
    rw [Functor.map_comp, Functor.map_comp]
    change (𝟙 S ≫ ((D.transport a.left).collapse ≫ augmentationCode V.left),
        degreeOperator a.left ≫ 𝟙 (degree V.left)) =
      ((D.collapse ≫ augmentationCode U.left) ≫ nativeOperator a.left,
        𝟙 (degree U.left) ≫ degreeOperator a.left)
    exact Prod.ext ((Category.id_comp _).trans (D.horizontal_transport a.left))
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  have hc : (codeOf (W := W) (x := x) (y := y)).map l =
      (codeOf (W := W) (x := x) (y := y)).map r := by
    dsimp only [l, r]
    rw [Functor.map_comp, Functor.map_comp]
    change 𝟙 S ≫ (D.collapse ≫ a.left.fiber.left) = D.collapse ≫ a.left.fiber.left
    exact Category.id_comp _
  apply JTTargetCommaPullback.operator_ext
    (F := DecoratedCylinderNecklacePresentation.underDiagram W x y) (hc := hc)
  apply Quiver.Hom.unop_inj
  apply Subtype.ext
  exact congrArg (fun f ↦ f.op) hb

end

end DaggerModels.PartII.JTGraphTransportNaturality
