import DaggerModelsPartII.JTGraphVariableTimeIndex
import DaggerModelsPartII.JTGraphNativeLabelDiagram
import DaggerModelsPartII.JTGraphInterpolatedSourceComparison

/-! The full variable-source graph resolution compares inside the original slice. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTGraphVariableTimeTraversal

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphVariableTimeIndex
open JTGraphLiftTransport (GraphLift)
open JTGraphInterpolatedRaw (index toDecorated whole_raw)
open JTGraphInterpolatedComparison (decorated_reindex)
open JTGraphInterpolatedCollapseOriginal (pullbackLift pullback_collapse timeCollapse)
open JTGraphInterpolatedSourceComparison (sourceMap)
open JTNecklaceEndpointCylinder (under value nativeMap)
open DecoratedCylinderNecklacePresentation (underDiagram underCocone)
open BoundaryNecklaceComma (necklaceUnder)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable (U : TargetComma Q)

private abbrev obj (P : Index U) := (toNative U).obj P
private abbrev code (P : Index U) := (obj U P).left
private abbrev collapse (P : Index U) := (obj U P).hom
private abbrev time (P : Index U) := (JTGraphVariableTimeIndex.degree U).obj P
/-- The original pulled labels for every native source and time. -/
abbrev labels := toNative U ⋙ JTGraphNativeLabelDiagram.diagram U
/-- The full ordered cylinder diagram in the source and time. -/
abbrev cylinders := joint U ⋙ NecklaceCylinderJointDiagram.cylinderUnder

private def decorated (P : Index U) :
    (cylinders U).obj P ⟶ (underDiagram W x y).obj ((labels U).obj P) :=
  toDecorated U (collapse U P) (fun i ↦ (family U P i).parameter)

private theorem whole (P : Index U) :
    (decorated U P).right ≫ ((underCocone W x y).app ((labels U).obj P)).right =
      NecklaceCylinderAugmentation.augmentation (code U P) (time U P) ≫
        (collapse U P ≫ U.hom.hom).map ≫ Q.map := by
  apply whole_raw
  intro i
  have h := (family U P i).comm
  rw [family_collapse U P i] at h
  exact h

private theorem cylinder_map {P P' : Index U} (f : P ⟶ P') :
    (cylinders U).map f = sourceMap ((toNative U).map f).left (time U P) ≫
      (under (code U P')).map ((JTGraphVariableTimeIndex.degree U).map f) := by
  apply Under.UnderMorphism.ext
  rfl

private theorem label_map_right {P P' : Index U} (f : P ⟶ P') :
    ((underDiagram W x y).map ((labels U).map f)).right =
      nativeMap ((toNative U).map f).left (JTGraphLiftTransport.degree U.left) := by
  change nativeMap ((toNative U).map f).left (JTGraphLiftTransport.degree U.left) ≫
      (value (code U P')).map (𝟙 (JTGraphLiftTransport.degree U.left)) = _
  rw [(value (code U P')).map_id]
  exact Category.comp_id _

private theorem decorated_natural {P P' : Index U} (f : P ⟶ P') :
    (decorated U P) ≫ (underDiagram W x y).map ((labels U).map f) =
      (cylinders U).map f ≫ decorated U P' := by
  let g := ((toNative U).map f).left
  let j := (JTGraphVariableTimeIndex.degree U).map f
  let a := fun i ↦ (family U P' i).parameter
  have hf : (fun i ↦ (family U P i).parameter) = fun i ↦ g.map ≫ a (j.toOrderHom i) := by
    funext i
    exact congrArg GraphLift.parameter (family_map U f i)
  apply Under.UnderMorphism.ext
  change (decorated U P).right ≫ ((underDiagram W x y).map ((labels U).map f)).right =
    ((cylinders U).map f).right ≫ (decorated U P').right
  rw [cylinder_map, label_map_right]
  change JTInterpolatedReducedCylinder.cylinderMap (code U P)
      (JTGraphParameterInterpolation.interpolate (fun i ↦ (family U P i).parameter)) ≫
        nativeMap g (JTGraphLiftTransport.degree U.left) =
      (nativeMap g (time U P) ≫ (value (code U P')).map j) ≫
        JTInterpolatedReducedCylinder.cylinderMap (code U P')
          (JTGraphParameterInterpolation.interpolate a)
  rw [hf, JTInterpolatedCylinderSource.interpolated_source g (fun i ↦ a (j.toOrderHom i))]
  rw [Category.assoc]
  apply congrArg (nativeMap g (time U P) ≫ ·)
  exact (congrArg (fun k ↦ k.right)
    (decorated_reindex (collapse U P') (family U P') j)).symm

private theorem augmentation_change {P P' : Index U} (f : P ⟶ P') :
    ((cylinders U).map f).right ≫
      NecklaceCylinderAugmentation.augmentation (code U P') (time U P') =
    NecklaceCylinderAugmentation.augmentation (code U P) (time U P) ≫
      ((toNative U).map f).left.map :=
  NecklaceCylinderJointDiagram.augmentation.naturality ((joint U).map f)

private theorem native_natural {P P' : Index U} (f : P ⟶ P') :
    JTCylinderOverTarget.native W x y Q (code U P) (time U P)
        (collapse U P ≫ U.hom.hom) =
      (cylinders U).map f ≫ JTCylinderOverTarget.native W x y Q (code U P') (time U P')
        (collapse U P' ≫ U.hom.hom) := by
  apply Under.UnderMorphism.ext
  let g := ((toNative U).map f).left
  let a := NecklaceCylinderAugmentation.augmentation (code U P) (time U P)
  change a ≫ (collapse U P ≫ U.hom.hom).map =
    ((cylinders U).map f).right ≫
      (NecklaceCylinderAugmentation.augmentation (code U P') (time U P') ≫
        (collapse U P' ≫ U.hom.hom).map)
  rw [← Category.assoc, augmentation_change U f, Category.assoc]
  have h : collapse U P ≫ U.hom.hom = g ≫ (collapse U P' ≫ U.hom.hom) := by
    rw [← Category.assoc, Over.w ((toNative U).map f)]
  exact congrArg (fun v : code U P ⟶ Q.code ↦ a ≫ v.map) h

/-- The decorated traversal respects all original source and time operators. -/
def decoratedNatural : cylinders U ⟶ labels U ⋙ underDiagram W x y where
  app := decorated U
  naturality {_ _} f := (decorated_natural U f).symm

/-- The complete map into the fixed native target respects both operators. -/
def targetNatural : cylinders U ⟶ (Functor.const _).obj (necklaceUnder.obj Q.code) where
  app P := JTCylinderOverTarget.native W x y Q (code U P) (time U P)
    (collapse U P ≫ U.hom.hom)
  naturality {_ _} f := (native_natural U f).symm.trans (Category.comp_id _).symm

/-- The natural pair agrees over the same full raw target map. -/
theorem pair_square (P : Index U) :
    (decoratedNatural U).app P ≫ (underCocone W x y).app ((labels U).obj P) =
      (targetNatural U).app P ≫ JTTargetCommaPullback.targetMap W x y Q := by
  apply Under.UnderMorphism.ext
  change (decorated U P).right ≫ ((underCocone W x y).app ((labels U).obj P)).right =
    (NecklaceCylinderAugmentation.augmentation (code U P) (time U P) ≫
      (collapse U P ≫ U.hom.hom).map) ≫ Q.map
  exact (whole U P).trans (Category.assoc _ _ _).symm


end
end DaggerModels.PartII.JTGraphVariableTimeTraversal
