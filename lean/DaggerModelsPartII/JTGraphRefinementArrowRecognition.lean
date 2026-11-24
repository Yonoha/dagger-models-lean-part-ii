import DaggerModelsPartII.JTGraphRefinementMixedArrow
import DaggerModelsPartII.JTGraphLiftTransport

/-!
# Recover a mixed graph arrow from an arrow of the original target comma

The horizontal code and the native collapse are already determined in
the comma. Only the equality of the full parameters needs to be checked.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory
open DaggerChosenRigidificationNecklace CartesianMonoidalCategory

namespace DaggerModels.PartII.JTGraphRefinementArrowRecognition

open JTGraphRefinement JTGraphRefinementMixedArrow JTNecklaceEndpointCylinder
open JTProjectiveOrderedFiberComparison (row)
open JTCommaGraphPredecessor (augmentationCode)
open JTGraphLiftTransport (augmentationCode_natural traversal_natural)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {D E : Refinement W x y Q}

private theorem augmentation_identity (D : Refinement W x y Q) :
    augmentationCode D.toComma.left = 𝟙 D.code := by
  apply NecklaceCode.Hom.ext
  change (lift (𝟙 D.code.toSSet) D.parameter ≫ (cylinder D.code).app D.degree) ≫
    NecklaceCylinderAugmentation.augmentation D.code D.degree = 𝟙 _
  rw [Category.assoc, NecklaceCylinderAugmentation.augmentation_cylinder, lift_fst]

variable (a : D.toComma ⟶ E.toComma)

/-- The graph's inner and outer native operators agree in every actual comma arrow. -/
theorem native_eq : a.left.fiber.left = (projection.map a.left.base).1 := by
  have h := augmentationCode_natural a.left
  rw [augmentation_identity, augmentation_identity] at h
  exact (Category.comp_id _).symm.trans (h.trans (Category.id_comp _))

private abbrev u := (projection.map a.left.base).1
private abbrev b := (projection.map a.left.base).2

/-- The actual arrow gives equality of both traversals in the reduced cylinder. -/
theorem reduced_eq :
    lift (u a).map (D.parameter ≫ J.map (b a)) ≫ (cylinder E.code).app E.degree =
      lift (u a).map ((u a).map ≫ E.parameter) ≫ (cylinder E.code).app E.degree := by
  have h := traversal_natural a.left
  change a.left.fiber.left.map ≫
      (lift (𝟙 E.code.toSSet) E.parameter ≫ (cylinder E.code).app E.degree) =
      (lift (𝟙 D.code.toSSet) D.parameter ≫
      (cylinder D.code).app D.degree) ≫
        (nativeMap (u a) D.degree ≫ (value E.code).map (b a)) at h
  rw [native_eq a] at h
  calc
    _ = (lift (𝟙 D.code.toSSet) D.parameter ≫ (cylinder D.code).app D.degree) ≫
        (nativeMap (u a) D.degree ≫ (value E.code).map (b a)) :=
      (traversal_map (u a) (b a) D.parameter).symm
    _ = (u a).map ≫ lift (𝟙 E.code.toSSet) E.parameter ≫ (cylinder E.code).app E.degree :=
      h.symm
    _ = _ := by
      rw [← Category.assoc, CartesianMonoidalCategory.comp_lift]
      have hId : (u a).map ≫ 𝟙 E.code.toSSet = (u a).map := Category.comp_id _
      exact congrArg (fun g ↦ lift g ((u a).map ≫ E.parameter) ≫
        (cylinder E.code).app E.degree) hId

/-- The full parameter equation lifts an actual comma arrow to a strict mixed arrow. -/
def recover (h : D.parameter ≫ J.map (b a) = (u a).map ≫ E.parameter) : D ⟶ E where
  label := a.left.base
  parameter := h
  collapse := by
    rw [← native_eq a]
    exact congrArg (fun f ↦ f.hom) (CostructuredArrow.w a)

theorem evaluate_recover (h : D.parameter ≫ J.map (b a) = (u a).map ≫ E.parameter) :
    (evaluate Q).map (recover a h) = a := by
  apply CostructuredArrow.hom_ext
  apply JTTargetCommaPullback.operator_ext
  · rfl
  · exact (native_eq a).symm

end

end DaggerModels.PartII.JTGraphRefinementArrowRecognition
