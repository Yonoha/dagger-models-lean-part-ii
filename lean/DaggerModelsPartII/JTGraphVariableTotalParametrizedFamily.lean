import DaggerModelsPartII.JTGraphVariableTotalCylinder
import DaggerModelsPartII.JTGraphVariableParametrizedFamilyTransport

/-!
Assemble the existing coherent graph families over the entire original
variable-source resolution. The old total labels and joint diagram supply
the index operators; existing fiber naturality and original-target transport
supply the two parts of the global family law. No prism lift is chosen anew.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 100000

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphVariableTotalParametrizedFamily

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphVariableResolutionCategory (Total totalJoint totalJoint_map totalLabels totalLabels_map)
open JTGraphVariableTimeIndex (toNative)
open JTGraphVariableTimeTransport (transport)
open JTGraphVariableParametrizedFamily (coherentFamily)
open JTGraphVariableParametrizedFamilyTransport (parameter_transport collapse_transport)
open JTGraphVariableLabelTransport (labelTransport_projection)
open JTGraphLiftTransport (degreeOperator)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev ops (W : Source) (x y : Vertex W) :=
  OrderedLabelElements.projection W (OrderedNecklaceVertexPoints.boundaryPoint W x y)

variable {W : Source} {x y : Vertex W}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))

/-- Keep the actual time of the existing total resolution. -/
abbrev time : Total Q ⥤ SimplexCategory :=
  totalJoint Q ⋙ CategoryTheory.Prod.snd NecklaceCode SimplexCategory

/-- The mixed native and coefficient operators are the original inner
native operator and outer coefficient operator. -/
theorem operators_map {P P' : Total Q} (f : P ⟶ P') :
    (ops W x y).map ((totalLabels Q).map f) =
      (((toNative P'.base).map f.fiber.base).left, degreeOperator f.base.left) := by
  have hi := JTGraphNativeLabelDiagram.diagram_map P'.base
    ((toNative P'.base).map f.fiber.base)
  change (ops W x y).map
      ((JTGraphVariableTimeTraversal.labels P'.base).map f.fiber.base) = _ at hi
  rw [totalLabels_map, Functor.map_comp, labelTransport_projection, hi]
  exact Prod.ext (Category.id_comp _) (Category.comp_id _)

/-- The outer transport keeps the whole time coordinate unchanged. -/
theorem time_map {P P' : Total Q} (f : P ⟶ P') :
    (time Q).map f = (JTGraphVariableTimeIndex.degree P'.base).map f.fiber.base :=
  congrArg Prod.snd (totalJoint_map Q f)

/-- The actual full groupoid parameter at an object of the old resolution. -/
abbrev parameter (P : Total Q) := (coherentFamily P.base).parameter P.fiber.base

/-- The original native collapse is composed with the same fixed-target map. -/
def collapse : JTParametrizedTargetFamilies.codes (totalLabels Q) ⟶
    (Functor.const (Total Q)).obj Q.code where
  app P := ((toNative P.base).obj P.fiber.base).hom ≫ P.base.hom.hom
  naturality {P P'} f := by
    change ((ops W x y).map ((totalLabels Q).map f)).1 ≫
        (((toNative P'.base).obj P'.fiber.base).hom ≫ P'.base.hom.hom) =
      (((toNative P.base).obj P.fiber.base).hom ≫ P.base.hom.hom) ≫ 𝟙 Q.code
    rw [operators_map]
    have hc := Over.w ((toNative P'.base).map f.fiber.base)
    change ((toNative P'.base).map f.fiber.base).left ≫
        ((toNative P'.base).obj P'.fiber.base).hom =
      ((toNative P.base).obj P.fiber.base).hom ≫ f.base.left.fiber.left at hc
    calc
      _ = (((toNative P'.base).map f.fiber.base).left ≫
          ((toNative P'.base).obj P'.fiber.base).hom) ≫ P'.base.hom.hom :=
        (Category.assoc _ _ _).symm
      _ = (((toNative P.base).obj P.fiber.base).hom ≫
          f.base.left.fiber.left) ≫ P'.base.hom.hom :=
        congrArg (fun h ↦ h ≫ P'.base.hom.hom) hc
      _ = ((toNative P.base).obj P.fiber.base).hom ≫ P.base.hom.hom :=
        collapse_transport f.base P.fiber.base
      _ = _ := (Category.comp_id _).symm

/-- The parameters obey both the old fiber law and the old original-target
transport law, on the full existing total category. -/
theorem parameter_map {P P' : Total Q} (f : P ⟶ P') :
    (((ops W x y).map ((totalLabels Q).map f)).1.map ⊗ₘ
        J.map ((time Q).map f)) ≫ parameter Q P' =
      parameter Q P ≫ J.map ((ops W x y).map ((totalLabels Q).map f)).2 := by
  rw [operators_map, time_map]
  have hi := (coherentFamily P'.base).parameter_map f.fiber.base
  change (((toNative P'.base).map f.fiber.base).left.map ⊗ₘ
      J.map ((JTGraphVariableTimeIndex.degree P'.base).map f.fiber.base)) ≫
      (coherentFamily P'.base).parameter P'.fiber.base =
    (coherentFamily P'.base).parameter ((transport f.base).obj P.fiber.base) ≫
      J.map (𝟙 (JTGraphLiftTransport.degree P'.base.left)) at hi
  have hid :
      (coherentFamily P'.base).parameter ((transport f.base).obj P.fiber.base) ≫
          J.map (𝟙 (JTGraphLiftTransport.degree P'.base.left)) =
        (coherentFamily P'.base).parameter ((transport f.base).obj P.fiber.base) :=
    (congrArg
      (fun h ↦ (coherentFamily P'.base).parameter
        ((transport f.base).obj P.fiber.base) ≫ h)
      (J.map_id (JTGraphLiftTransport.degree P'.base.left))).trans
        (Category.comp_id _)
  exact hi.trans (hid.trans (parameter_transport f.base P.fiber.base))

/-- One strict full fixed-Q family on the existing resolution of ALL
original comma objects and arrows, with no new natural-choice premise. -/
def family : JTParametrizedTargetFamilies.Family Q (totalLabels Q) (time Q) where
  collapse := collapse Q
  parameter := parameter Q
  parameter_map f := parameter_map Q f
  raw P := (coherentFamily P.base).raw P.fiber.base

end
end DaggerModels.PartII.JTGraphVariableTotalParametrizedFamily
