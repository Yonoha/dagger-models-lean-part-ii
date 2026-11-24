import DaggerModelsPartII.JTGraphRestrictionRaw
import DaggerModelsPartII.JTGraphTransportNaturality
import DaggerModelsPartII.JTTargetCommaPullbackComparison

/-!
# Natural restriction of actual graph predecessors over a fixed raw target
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphRestrictionNaturality

open JTProjectiveOrderedFiberComparison JTGraphLiftTransport JTGraphLiftRestriction
open JTGraphRestrictionRaw (predecessor commaRestriction restrictionArrow)
open JTGraphTransportNaturality (toComma)
open JTCommaGraphPredecessor (augmentationCode)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}

private abbrev F := DecoratedCylinderNecklacePresentation.toTarget W x y
variable {U : CostructuredArrow (F (W := W) (x := x) (y := y)) Q}
variable {S T : NecklaceCode}

private abbrev baseOf := DecoratedCylinderNecklacePresentation.projection W x y ⋙
  projection (W := W) (x := x) (y := y)
private abbrev codeOf :=
  BoundaryNecklaceComma.sourceCode (DecoratedCylinderNecklacePresentation.underDiagram W x y)

/-- Native restriction commutes with comparison to the original object in the actual comma. -/
theorem commaRestriction_natural (E : GraphLift U.left T) (g : S ⟶ T) :
    commaRestriction E g ≫ toComma E = toComma (restrict E g) := by
  apply CostructuredArrow.hom_ext
  let l := (commaRestriction E g).left ≫ (toComma E).left
  let r := (toComma (restrict E g)).left
  change l = r
  have hb : (baseOf (W := W) (x := x) (y := y)).map l =
      (baseOf (W := W) (x := x) (y := y)).map r := by
    dsimp only [l, r]
    rw [Functor.map_comp]
    change (g ≫ (E.collapse ≫ augmentationCode U.left),
        𝟙 (degree U.left) ≫ 𝟙 (degree U.left)) =
      ((restrict E g).collapse ≫ augmentationCode U.left,
        𝟙 (degree U.left))
    exact Prod.ext (Category.assoc _ _ _).symm (Category.id_comp _)
  have hc : (codeOf (W := W) (x := x) (y := y)).map l =
      (codeOf (W := W) (x := x) (y := y)).map r := by
    dsimp only [l, r]
    rw [Functor.map_comp]
    change g ≫ E.collapse = (restrict E g).collapse
    rfl
  apply JTTargetCommaPullback.operator_ext
    (F := DecoratedCylinderNecklacePresentation.underDiagram W x y) (hc := hc)
  apply Quiver.Hom.unop_inj
  apply Subtype.ext
  exact congrArg (fun f ↦ f.op) hb

end

end DaggerModels.PartII.JTGraphRestrictionNaturality
