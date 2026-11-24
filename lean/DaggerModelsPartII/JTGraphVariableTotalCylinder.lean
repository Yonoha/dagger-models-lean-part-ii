import DaggerModelsPartII.JTGraphVariableResolutionCategory
import DaggerModelsPartII.JTGraphVariableLabelTransport
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-! The joint cylinder and decorated labels on the total variable-source resolution. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphVariableResolutionCategory

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphVariableTimeIndex (Resolution joint toNative)
open JTGraphVariableTimeTraversal (cylinders labels)
open JTGraphVariableTimeTransport (resolutionDiagram transportResolution)
open JTGraphVariableLabelTransport (labelTransport labelTransport_projection)
open JTGraphLiftTransport (projection degreeOperator)
open BoundaryNecklaceComma (fiberDiagram sourceCode necklaceUnder evaluation)

noncomputable section

section Projection

variable {B D : Type} [SmallCategory B] [SmallCategory D]
variable {F : B ⥤ Cat.{0, 0}} (P : ∀ b, F.obj b ⥤ D)
variable (h : ∀ {b b'} (f : b ⟶ b'), (F.map f).toFunctor ⋙ P b' = P b)

/-- A strictly invariant family of functors defines a functor from the total category. -/
private def strictGrothendieckProjection : Grothendieck F ⥤ D :=
  Grothendieck.functorFrom P (fun f ↦ eqToHom (h f).symm)
    (fun b ↦ by rfl)
    (fun _ _ _ f g ↦ by
      apply NatTrans.ext
      funext i
      simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app]
      simp only [eqToHom_trans])

private theorem strictGrothendieckProjection_map {z z' : Grothendieck F} (f : z ⟶ z') :
    (strictGrothendieckProjection P h).map f =
      eqToHom (Functor.congr_obj (h f.base).symm z.fiber) ≫ (P z'.base).map f.fiber := by
  simp only [strictGrothendieckProjection, Grothendieck.functorFrom_map, eqToHom_app]


end Projection

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))

/-- The Grothendieck construction over all original comma objects. -/
abbrev Total := Grothendieck (resolutionDiagram Q)

variable {Q} in
private abbrev fiberJoint (U : TargetComma Q) : Resolution U ⥤ NecklaceCode × SimplexCategory :=
  Grothendieck.forget (fiberDiagram (cylinders U)) ⋙ joint U

variable {Q} in
private abbrev fiberCode (U : TargetComma Q) : Resolution U ⥤ NecklaceCode :=
  sourceCode (cylinders U)

variable {Q} in
private theorem joint_transport {U V : TargetComma Q} (a : U ⟶ V) :
    transportResolution a ⋙ fiberJoint V = fiberJoint U := rfl

variable {Q} in
private theorem code_transport {U V : TargetComma Q} (a : U ⟶ V) :
    transportResolution a ⋙ fiberCode V = fiberCode U := rfl

/-- The joint native source and time of every cylinder in the total resolution. -/
def totalJoint : Total Q ⥤ NecklaceCode × SimplexCategory :=
  strictGrothendieckProjection (fiberJoint (Q := Q)) (fun a ↦ joint_transport a)

/-- The actual internal necklace in the total resolution. -/
def totalCode : Total Q ⥤ NecklaceCode :=
  strictGrothendieckProjection (fiberCode (Q := Q)) (fun a ↦ code_transport a)

/-- Transport on the outer comma arrow retains the joint source and time. -/
theorem totalJoint_map {P P' : Total Q} (f : P ⟶ P') :
    (totalJoint Q).map f = (fiberJoint P'.base).map f.fiber := by
  change (strictGrothendieckProjection _ _).map f = _
  rw [strictGrothendieckProjection_map]
  exact Category.id_comp _

/-- Transport on the outer comma arrow retains the internal necklace. -/
theorem totalCode_map {P P' : Total Q} (f : P ⟶ P') :
    (totalCode Q).map f = (fiberCode P'.base).map f.fiber := by
  change (strictGrothendieckProjection _ _).map f = _
  rw [strictGrothendieckProjection_map]
  exact Category.id_comp _

/-- The actual full internal traversal, natural in the outer comma operator
as well as the inner source, time, and necklace operators. -/
def totalEvaluation : totalCode Q ⋙ necklaceUnder ⟶
    totalJoint Q ⋙ NecklaceCylinderJointDiagram.cylinderUnder where
  app P := P.fiber.fiber.hom
  naturality {P P'} f := by
    change necklaceUnder.map ((totalCode Q).map f) ≫ P'.fiber.fiber.hom =
      P.fiber.fiber.hom ≫ NecklaceCylinderJointDiagram.cylinderUnder.map ((totalJoint Q).map f)
    rw [totalCode_map, totalJoint_map]
    exact (evaluation (cylinders P'.base)).naturality f.fiber


private abbrev Label := DecoratedNecklaceHomDiagram.Index W x y
private abbrev operators := projection (W := W) (x := x) (y := y)

private instance : (operators (W := W) (x := x) (y := y)).Faithful := by
  change ((CategoryOfElements.π _).leftOp).Faithful
  infer_instance

private abbrev outerLabel : TargetComma Q ⥤ Label (W := W) (x := x) (y := y) :=
  CostructuredArrow.proj (DecoratedCylinderNecklacePresentation.toTarget W x y) Q ⋙
    DecoratedCylinderNecklacePresentation.projection W x y

private abbrev outerDegree : TargetComma Q ⥤ SimplexCategory :=
  outerLabel Q ⋙ operators ⋙ CategoryTheory.Prod.snd NecklaceCode SimplexCategory

private def totalOperators : Total Q ⥤ NecklaceCode × SimplexCategory :=
  ((totalJoint Q) ⋙ CategoryTheory.Prod.fst _ _).prod'
    (Grothendieck.forget (resolutionDiagram Q) ⋙ outerDegree Q)

private def labelObj (P : Total Q) : Label (W := W) (x := x) (y := y) :=
  (labels P.base).obj P.fiber.base

private def labelArrow {P P' : Total Q} (f : P ⟶ P') : labelObj Q P ⟶ labelObj Q P' :=
  (labelTransport f.base).app P.fiber.base ≫ (labels P'.base).map f.fiber.base

private theorem labelArrow_projection {P P' : Total Q} (f : P ⟶ P') :
    (operators (W := W) (x := x) (y := y)).map (labelArrow Q f) = (totalOperators Q).map f := by
  let F := operators (W := W) (x := x) (y := y)
  rw [labelArrow, F.map_comp, labelTransport_projection]
  have h := JTGraphNativeLabelDiagram.diagram_map P'.base ((toNative P'.base).map f.fiber.base)
  change F.map ((labels P'.base).map f.fiber.base) = _ at h
  rw [h]
  have hm := totalJoint_map Q f
  have hl := congrArg (fun g ↦ g.1) hm
  change (𝟙 ((toNative P.base).obj P.fiber.base).left ≫ ((toNative P'.base).map f.fiber.base).left,
      degreeOperator f.base.left ≫ 𝟙 (JTGraphLiftTransport.degree P'.base.left)) =
    (((totalJoint Q).map f).1, degreeOperator f.base.left)
  exact Prod.ext ((Category.id_comp _).trans hl.symm) (Category.comp_id _)

/-- The original decorated labels on the total cylinder resolution. -/
def totalLabels : Total Q ⥤ Label (W := W) (x := x) (y := y) :=
  Functor.Faithful.div (totalOperators Q) operators (labelObj Q)
    (fun _ ↦ rfl) (labelArrow Q) (fun {_ _} {f} ↦ heq_of_eq (labelArrow_projection Q f))

/-- The outer label transport is followed by the original label operator of the fiber arrow. -/
theorem totalLabels_map {P P' : Total Q} (f : P ⟶ P') :
    (totalLabels Q).map f =
      (labelTransport f.base).app P.fiber.base ≫ (labels P'.base).map f.fiber.base := rfl


end
end DaggerModels.PartII.JTGraphVariableResolutionCategory
