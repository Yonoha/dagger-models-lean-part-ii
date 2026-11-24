import DaggerModelsPartII.JTGraphVariableLabelTransport
import DaggerModelsPartII.JTGraphVariableTimeComparison

/-! The two literal operator triangles for source-time resolution transport. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphVariableComparisonConesOperators

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphVariableTimeIndex
open JTGraphVariableTimeTransport (transport)
open JTGraphVariableLabelTransport (labelTransport labelTransport_projection)
open JTGraphLiftTransport (projection augmentationCode_natural degreeOperator)
open JTCommaGraphPredecessor (augmentationCode)
open JTGraphNativeLabelDiagram (toOriginal toOriginal_app)
open JTGraphInterpolatedCollapseOriginal (indexCollapse_operator)
open JTGraphVariableTimeComparison (decoratedCollapse nativeCollapse)
open BoundaryNecklaceComma (necklaceUnder)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {U V : TargetComma Q} (a : U ⟶ V)

private theorem label_collapse_operator (A : TargetComma Q) (P : Index A) :
    (projection (W := W) (x := x) (y := y)).map ((toOriginal A).app ((toNative A).obj P)) =
      (((toNative A).obj P).hom ≫ augmentationCode A.left,
        𝟙 (JTGraphLiftTransport.degree A.left)) := by
  rw [toOriginal_app A ((toNative A).obj P) (family A P) (family_collapse A P),
    indexCollapse_operator]

/-- The original decorated operators commute with the variable-source comparison. -/
theorem label_triangle (P : Index U) :
    (labelTransport a).app P ≫ (decoratedCollapse V).app ((transport a).obj P) =
      (decoratedCollapse U).app P ≫ a.left.base := by
  let H := projection (W := W) (x := x) (y := y)
  let P' := (transport a).obj P
  let S := ((toNative U).obj P).left
  let c := ((toNative U).obj P).hom
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  suffices hh : H.map ((labelTransport a).app P ≫
        (decoratedCollapse V).app P') =
      H.map ((decoratedCollapse U).app P ≫ a.left.base) by
    exact congrArg (fun p ↦ p.op) hh
  change H.map (_ ≫ _) = H.map (_ ≫ _)
  rw [H.map_comp, H.map_comp, labelTransport_projection a P]
  change _ ≫ H.map ((toOriginal V).app ((toNative V).obj P')) =
    H.map ((toOriginal U).app ((toNative U).obj P)) ≫ _
  rw [label_collapse_operator V P',
    label_collapse_operator U P]
  change (𝟙 S ≫ (c ≫ a.left.fiber.left) ≫ augmentationCode V.left,
      degreeOperator a.left ≫ 𝟙 (JTGraphLiftTransport.degree V.left)) =
    ((c ≫ augmentationCode U.left) ≫ JTGraphLiftTransport.nativeOperator a.left,
      𝟙 (JTGraphLiftTransport.degree U.left) ≫ degreeOperator a.left)
  apply Prod.ext
  · rw [Category.id_comp, Category.assoc, augmentationCode_natural, Category.assoc]
  · change degreeOperator a.left ≫ 𝟙 _ = 𝟙 _ ≫ degreeOperator a.left
    exact (Category.comp_id _).trans (Category.id_comp _).symm


/-- The native part is the original cylinder augmentation on both sides. -/
theorem native_triangle (P : Index U) :
    HEq ((nativeCollapse V).app ((transport a).obj P))
      ((nativeCollapse U).app P ≫ necklaceUnder.map a.left.fiber.left) := by
  apply heq_of_eq
  apply Under.UnderMorphism.ext
  exact (Category.assoc _ _ _).symm

end
end DaggerModels.PartII.JTGraphVariableComparisonConesOperators
