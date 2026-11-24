import DaggerModelsPartII.JTCylinderOverTarget


set_option autoImplicit false

open CategoryTheory

universe u v u' v'

namespace DaggerModels.PartII.JTTargetCommaPullbackSliceProjection

variable {C : Type u} [Category.{v} C] {G : Type u'} [Category.{v'} G]
variable (e : C ≌ G) {P Q : G} {X Y : C}
variable (hP : e.functor.obj X = P) (hQ : e.functor.obj Y = Q)

private def equivalenceComparisonIso : e.inverse.obj P ≅ X :=
  (e.inverse.mapIso (eqToIso hP.symm)).trans (e.unitIso.app X).symm

private theorem equivalenceComparisonArrow (f : P ⟶ Q) :
    e.functor.map
      ((equivalenceComparisonIso e hP).inv ≫ e.inverse.map f ≫ (equivalenceComparisonIso e hQ).hom) =
        eqToHom hP ≫ f ≫ eqToHom hQ.symm := by
  cases hP
  cases hQ
  simp only [equivalenceComparisonIso, eqToIso_refl, Functor.mapIso_refl, Iso.refl_trans,
    Iso.symm_inv, Iso.symm_hom, eqToHom_refl, Category.id_comp, Category.comp_id,
    Functor.map_comp]
  change e.functor.map (e.unit.app X) ≫ e.functor.map (e.inverse.map f) ≫
    e.functor.map (e.unitInv.app Y) = f
  rw [← e.counitInv_app_functor X, ← e.counit_app_functor Y]
  rw [← Category.assoc, e.counitInv_naturality]
  simp

end DaggerModels.PartII.JTTargetCommaPullbackSliceProjection

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTTargetCommaPullbackSliceProjection

open JTTargetCommaPullback JTNecklaceEndpointCylinder NecklaceCylinderAugmentation
open DecoratedCylinderNecklacePresentation (underDiagram underCocone toTarget)
open BoundaryNecklaceComma (necklaceUnder)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable (W : Source) (x y : Vertex W)
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))

theorem pair_fromObj (R : JTTargetCommaPullback.Presentation W x y Q) :
    (toPullback W x y Q).obj (fromObj W x y Q R) = R := by
  have h : JTTargetCommaPullback.lift W x y Q (fromObj W x y Q R) = R.fiber.hom := by
    apply pullback.hom_ext (f := (underCocone W x y).app R.base)
      (g := targetMap W x y Q)
    · change JTTargetCommaPullback.lift W x y Q (fromObj W x y Q R) ≫
          fst W x y Q R.base = R.fiber.hom ≫ fst W x y Q R.base
      exact JTTargetCommaPullback.lift_fst W x y Q (fromObj W x y Q R)
    · change JTTargetCommaPullback.lift W x y Q (fromObj W x y Q R) ≫
          snd W x y Q R.base = R.fiber.hom ≫ snd W x y Q R.base
      exact (JTTargetCommaPullback.lift_snd W x y Q (fromObj W x y Q R)).trans
        (by apply Under.UnderMorphism.ext; rfl)
  exact congrArg (fun m ↦ ⟨R.base, CostructuredArrow.mk m⟩ :
    _ → JTTargetCommaPullback.Presentation W x y Q) h

def comparisonIso (R : JTTargetCommaPullback.Presentation W x y Q) :
    (equivalence W x y Q).inverse.obj R ≅ fromObj W x y Q R :=
  ((equivalence W x y Q).inverse.mapIso
    (eqToIso (pair_fromObj W x y Q R).symm)).trans
      ((equivalence W x y Q).unitIso.app (fromObj W x y Q R)).symm

theorem comparison_arrow {R S : JTTargetCommaPullback.Presentation W x y Q}
    (f : R ⟶ S) :
    (equivalence W x y Q).functor.map
      ((comparisonIso W x y Q R).inv ≫
        (equivalence W x y Q).inverse.map f ≫
          (comparisonIso W x y Q S).hom) =
      eqToHom (pair_fromObj W x y Q R) ≫ f ≫
        eqToHom (pair_fromObj W x y Q S).symm :=
  equivalenceComparisonArrow (equivalence W x y Q)
    (pair_fromObj W x y Q R) (pair_fromObj W x y Q S) f

private abbrev Input (T : NecklaceCode) (n : SimplexCategory) :=
  CostructuredArrow necklaceUnder ((JTNecklaceEndpointCylinder.under T).obj n)

private abbrev Result (i : DecoratedNecklaceHomDiagram.Index W x y)
    (T : NecklaceCode) (n : SimplexCategory)
    (h : (JTNecklaceEndpointCylinder.under T).obj n ⟶ (underDiagram W x y).obj i)
    (d : T ⟶ Q.code)
    (hr : h.right ≫ ((underCocone W x y).app i).right =
      augmentation T n ≫ d.map ≫ Q.map)
    (P : Input T n) : JTTargetCommaPullback.Presentation W x y Q :=
  (Grothendieck.ι (BoundaryNecklaceComma.fiberDiagram (diagram W x y Q)) i).obj
    ((JTCylinderOverTarget.atBase W x y Q i T n h d hr).obj P)

theorem existingIso_eq (i : DecoratedNecklaceHomDiagram.Index W x y)
    (T : NecklaceCode) (n : SimplexCategory)
    (h : (JTNecklaceEndpointCylinder.under T).obj n ⟶ (underDiagram W x y).obj i)
    (d : T ⟶ Q.code)
    (hr : h.right ≫ ((underCocone W x y).app i).right =
      augmentation T n ≫ d.map ≫ Q.map)
    (P : Input T n) :
    JTCylinderOverTarget.functor_obj_iso W x y Q i T n h d hr P =
      comparisonIso W x y Q (Result W x y Q i T n h d hr P) := by
  rfl

theorem projected_cross_arrow
    (i₁ : DecoratedNecklaceHomDiagram.Index W x y)
    (T₁ : NecklaceCode) (n₁ : SimplexCategory)
    (h₁ : (JTNecklaceEndpointCylinder.under T₁).obj n₁ ⟶ (underDiagram W x y).obj i₁)
    (d₁ : T₁ ⟶ Q.code)
    (hr₁ : h₁.right ≫ ((underCocone W x y).app i₁).right =
      augmentation T₁ n₁ ≫ d₁.map ≫ Q.map)
    (P₁ : Input T₁ n₁)
    (i₂ : DecoratedNecklaceHomDiagram.Index W x y)
    (T₂ : NecklaceCode) (n₂ : SimplexCategory)
    (h₂ : (JTNecklaceEndpointCylinder.under T₂).obj n₂ ⟶ (underDiagram W x y).obj i₂)
    (d₂ : T₂ ⟶ Q.code)
    (hr₂ : h₂.right ≫ ((underCocone W x y).app i₂).right =
      augmentation T₂ n₂ ≫ d₂.map ≫ Q.map)
    (P₂ : Input T₂ n₂)
    (f : Result W x y Q i₁ T₁ n₁ h₁ d₁ hr₁ P₁ ⟶
      Result W x y Q i₂ T₂ n₂ h₂ d₂ hr₂ P₂) :
    (equivalence W x y Q).functor.map
      ((JTCylinderOverTarget.functor_obj_iso W x y Q i₁ T₁ n₁ h₁ d₁ hr₁ P₁).inv ≫
        (equivalence W x y Q).inverse.map f ≫
          (JTCylinderOverTarget.functor_obj_iso W x y Q i₂ T₂ n₂ h₂ d₂ hr₂ P₂).hom) =
      eqToHom (pair_fromObj W x y Q (Result W x y Q i₁ T₁ n₁ h₁ d₁ hr₁ P₁)) ≫
        f ≫
          eqToHom
            (pair_fromObj W x y Q (Result W x y Q i₂ T₂ n₂ h₂ d₂ hr₂ P₂)).symm := by
  rw [existingIso_eq W x y Q i₁ T₁ n₁ h₁ d₁ hr₁ P₁,
    existingIso_eq W x y Q i₂ T₂ n₂ h₂ d₂ hr₂ P₂]
  exact comparison_arrow W x y Q f

end
end DaggerModels.PartII.JTTargetCommaPullbackSliceProjection

