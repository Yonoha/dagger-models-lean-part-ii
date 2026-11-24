import DaggerModelsPartII.JTGraphVariableTimeTransport
import DaggerModelsPartII.JTGraphVariableTimeTraversal
import DaggerModelsPartII.JTGraphInterpolatedTransport

/-! Transport of decorated labels for every source and time operator. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphVariableLabelTransport

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphVariableTimeIndex
open JTGraphVariableTimeTraversal (labels)
open JTGraphVariableTimeTransport (transport transport_id transport_comp)
open JTGraphLiftTransport (degreeOperator projection)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {U V Z : TargetComma Q} (a : U ⟶ V)

private abbrev H := projection (W := W) (x := x) (y := y)

private def labelArrow (P : Index U) : (labels U).obj P ⟶ (labels V).obj ((transport a).obj P) :=
  JTGraphInterpolatedTransport.indexArrow ((toNative U).obj P).hom (family U P)
    (family_collapse U P) a

private theorem labelArrow_projection (P : Index U) :
    (H (W := W) (x := x) (y := y)).map (labelArrow a P) =
      (𝟙 ((toNative U).obj P).left, degreeOperator a.left) :=
  JTGraphInterpolatedTransport.indexArrow_projection ((toNative U).obj P).hom
    (family U P) (family_collapse U P) a

private theorem label_ext {P P' : DecoratedNecklaceHomDiagram.Index W x y} {f g : P ⟶ P'}
    (h : (H (W := W) (x := x) (y := y)).map f =
      (H (W := W) (x := x) (y := y)).map g) : f = g := by
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  exact congrArg (fun p ↦ p.op) h

/-- Target transport is natural in both the original source and the time simplex. -/
def labelTransport : labels U ⟶ transport a ⋙ labels V where
  app := labelArrow a
  naturality {P P'} f := by
    apply label_ext
    let F := H (W := W) (x := x) (y := y)
    change F.map ((labels U).map f ≫ labelArrow a P') =
      F.map (labelArrow a P ≫ (labels V).map ((transport a).map f))
    rw [F.map_comp, F.map_comp, labelArrow_projection a P, labelArrow_projection a P']
    have h₁ := JTGraphNativeLabelDiagram.diagram_map U ((toNative U).map f)
    have h₂ := JTGraphNativeLabelDiagram.diagram_map V ((toNative V).map ((transport a).map f))
    change F.map ((labels U).map f) = _ at h₁
    change F.map ((labels V).map ((transport a).map f)) = _ at h₂
    rw [h₁, h₂]
    change (((toNative U).map f).left ≫ 𝟙 _, 𝟙 _ ≫ degreeOperator a.left) =
      (𝟙 _ ≫ ((toNative U).map f).left, degreeOperator a.left ≫ 𝟙 _)
    simp only [Category.comp_id, Category.id_comp]

/-- Its two literal operators are the source identity and the original target degree map. -/
theorem labelTransport_projection (P : Index U) :
    (H (W := W) (x := x) (y := y)).map ((labelTransport a).app P) =
      (𝟙 ((toNative U).obj P).left, degreeOperator a.left) :=
  labelArrow_projection a P

private theorem compare_identity {A C D : Type*} [Category* A] [Category* C] [Category* D]
    (F : C ⥤ D) [F.Faithful] {L M : A ⥤ C} (h : L = M) (α : L ⟶ M)
    (hp : ∀ i, F.map (α.app i) = eqToHom (congrArg (fun P : A ⥤ C ↦ F.obj (P.obj i)) h)) :
    α = eqToHom h := by
  ext i
  apply F.map_injective
  rw [eqToHom_app, eqToHom_map]
  exact hp i

private theorem compare_composite {A C D : Type*} [Category* A] [Category* C] [Category* D]
    (F : C ⥤ D) [F.Faithful] {L M N P : A ⥤ C}
    (α : L ⟶ M) (β : M ⟶ N) (γ : L ⟶ P) (h : N = P)
    (hp : ∀ i, F.map (γ.app i) = F.map (α.app i) ≫ F.map (β.app i) ≫
      eqToHom (congrArg (fun R : A ⥤ C ↦ F.obj (R.obj i)) h)) :
    γ = α ≫ β ≫ eqToHom h := by
  ext i
  apply F.map_injective
  simp only [NatTrans.comp_app, eqToHom_app, F.map_comp, eqToHom_map]
  exact hp i

private instance : (H (W := W) (x := x) (y := y)).Faithful := by
  change ((CategoryOfElements.π _).leftOp).Faithful
  infer_instance

private def targetDegrees : TargetComma Q ⥤ SimplexCategory :=
  CostructuredArrow.proj (DecoratedCylinderNecklacePresentation.toTarget W x y) Q ⋙
    DecoratedCylinderNecklacePresentation.projection W x y ⋙
    H ⋙ CategoryTheory.Prod.snd NecklaceCode SimplexCategory

private theorem degree_id (U : TargetComma Q) :
    degreeOperator (show U ⟶ U from 𝟙 U).left = 𝟙 (JTGraphLiftTransport.degree U.left) :=
  (targetDegrees (Q := Q)).map_id U

private theorem degree_comp (a : U ⟶ V) (b : V ⟶ Z) :
    degreeOperator (a ≫ b).left = degreeOperator a.left ≫ degreeOperator b.left :=
  (targetDegrees (Q := Q)).map_comp a b

private theorem label_identity_eq (U : TargetComma Q) :
    labels U = transport (𝟙 U) ⋙ labels U :=
  (congrArg (· ⋙ labels U) (transport_id U)).symm

private theorem label_composite_eq (a : U ⟶ V) (b : V ⟶ Z) :
    transport a ⋙ transport b ⋙ labels Z = transport (a ≫ b) ⋙ labels Z :=
  (congrArg (· ⋙ labels Z) (transport_comp a b)).symm

/-- Transport along the identity is the canonical equality of label functors. -/
theorem labelTransport_id (U : TargetComma Q) :
    labelTransport (𝟙 U) = eqToHom (label_identity_eq U) := by
  apply compare_identity (H (W := W) (x := x) (y := y))
  intro i
  have h := labelTransport_projection (𝟙 U) i
  have e : (𝟙 ((toNative U).obj i).left, degreeOperator (show U ⟶ U from 𝟙 U).left) =
      𝟙 (((toNative U).obj i).left, JTGraphLiftTransport.degree U.left) :=
    Prod.ext rfl (degree_id U)
  exact h.trans (e.trans (eqToHom_refl _ _).symm)

/-- Transport along a composite is the pasted comparison of label functors. -/
theorem labelTransport_comp (a : U ⟶ V) (b : V ⟶ Z) :
    labelTransport (a ≫ b) =
      labelTransport a ≫ Functor.whiskerLeft (transport a) (labelTransport b) ≫
        eqToHom (label_composite_eq a b) := by
  apply compare_composite (H (W := W) (x := x) (y := y))
  intro i
  let S := ((toNative U).obj i).left
  let j := (transport a).obj i
  have h₁ := labelTransport_projection a i
  have h₂ := labelTransport_projection b j
  have h₃ := labelTransport_projection (a ≫ b) i
  let j₁ : (S, JTGraphLiftTransport.degree U.left) ⟶ (S, JTGraphLiftTransport.degree V.left) :=
    (𝟙 S, degreeOperator a.left)
  let j₂ : (S, JTGraphLiftTransport.degree V.left) ⟶ (S, JTGraphLiftTransport.degree Z.left) :=
    (𝟙 S, degreeOperator b.left)
  let j₃ : (S, JTGraphLiftTransport.degree U.left) ⟶ (S, JTGraphLiftTransport.degree Z.left) :=
    (𝟙 S, degreeOperator (a ≫ b).left)
  have e : j₃ = j₁ ≫ j₂ ≫ 𝟙 (S, JTGraphLiftTransport.degree Z.left) := by
    rw [Category.comp_id]
    exact Prod.ext (Category.id_comp (𝟙 S)).symm (degree_comp a b)
  exact h₃.trans (e.trans (congrArg₂ (· ≫ ·) h₁.symm
    (congrArg₂ (· ≫ ·) h₂.symm (eqToHom_refl _ _).symm)))

end
end DaggerModels.PartII.JTGraphVariableLabelTransport
