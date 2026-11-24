import DaggerModelsPartII.NecklaceCylinderJointDiagram
import SSetGluing

/-!
# Collapsing the lifted endpoint lines

An arbitrary covered product diagram with lifted boundary lines has a
reduced diagram under the original boundary. Weakness transfers from the
product projection through the exact endpoint pushout.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTEndpointReducedCover

noncomputable section

variable {I : Type} [SmallCategory I] {B : SSet.{0}}
variable {A X X' : I ⥤ SSet.{0}} (u : A ⟶ X')
variable (e : A ⟶ (Functor.const I).obj B)

/-- The pointwise ordered boundary of a diagram under a fixed simplicial set. -/
def boundary (Y : I ⥤ Under B) : (Functor.const I).obj B ⟶ Y ⋙ Under.forget B where
  app p := (Y.obj p).hom
  naturality p p' f := by
    change 𝟙 B ≫ (Y.obj p').hom = (Y.obj p).hom ≫ (Y.map f).right
    exact (Category.id_comp _).trans (Under.w (Y.map f)).symm

/-- The exact pushout collapsing the covered endpoint lines. -/
abbrev reduced : I ⥤ Under B :=
  Under.lift (pushout u e) (pushout.inr u e)

variable (Y : I ⥤ Under B) (a : X' ⟶ Y ⋙ Under.forget B)
variable (h : u ≫ a = e ≫ boundary Y)

/-- The unique natural map of reduced diagrams under their original boundary. -/
def descend : reduced u e ⟶ Y where
  app p := Under.homMk ((pushout.desc a (boundary Y) h).app p)
    (NatTrans.congr_app (pushout.inr_desc a (boundary Y) h) p)
  naturality _ _ f :=
    Under.UnderMorphism.ext ((pushout.desc a (boundary Y) h).naturality f)

theorem descend_cylinder (p : I) :
    (pushout.inl u e).app p ≫ ((descend u e Y a h).app p).right = a.app p :=
  NatTrans.congr_app (pushout.inl_desc a (boundary Y) h) p

variable {a} {h}
variable (π : X' ⟶ X) (d : A ⟶ X) (i : X ⟶ Y ⋙ Under.forget B)
variable (hu : u ≫ π = d) (hi : d ≫ i = e ≫ boundary Y)

include hu hi in
private theorem projection_square : u ≫ π ≫ i = e ≫ boundary Y := by
  rw [← Category.assoc, hu, hi]

/-- Reduce the product projection under the same ordered boundary. -/
def projection : reduced u e ⟶ Y :=
  descend u e Y (π ≫ i) (projection_square u e Y π d i hu hi)

open DaggerSSetGluing

/-- If the old boundary inclusion is monic, the product projection's
weak equivalence survives collapse of the same lifted endpoint lines. -/
theorem projection_weak (p : I)
    (sq : IsPushout (d.app p) (e.app p) (i.app p) (boundary Y |>.app p))
    [Mono (d.app p)] [WeakEquivalence (π.app p)] :
    WeakEquivalence ((projection u e Y π d i hu hi).app p).right := by
  have hu' : u.app p ≫ π.app p = d.app p := NatTrans.congr_app hu p
  letI : Mono (u.app p) := mono_of_mono_fac hu'
  have n : IsPushout (u.app p) (e.app p) ((pushout.inl u e).app p)
      ((pushout.inr u e).app p) :=
    (IsPushout.of_hasPushout u e).map ((evaluation I _).obj p)
  let m := ((projection u e Y π d i hu hi).app p).right
  have h₁ : (pushout.inl u e).app p ≫ m = π.app p ≫ i.app p :=
    descend_cylinder u e Y (π ≫ i) (projection_square u e Y π d i hu hi) p
  have h₂ : (pushout.inr u e).app p ≫ m = (boundary Y).app p :=
    Under.w ((projection u e Y π d i hu hi).app p)
  apply (weakEquivalence_iff_GW _).mpr
  exact geometric_of_pushout_cube _ _ _ _ _ _ _ _ n sq
    (𝟙 _) (π.app p) (𝟙 _) m
    (hu'.trans (Category.id_comp _).symm) ((Category.comp_id _).trans (Category.id_comp _).symm)
    h₁ (h₂.trans (Category.id_comp _).symm)
    ((weakEquivalence_iff_GW _).mp inferInstance)
    ((weakEquivalence_iff_GW _).mp inferInstance)
    ((weakEquivalence_iff_GW _).mp inferInstance)

/-- Each component of a trivial-fibration cover has a section preserving
the entire boundary, and its descent is a section of the reduced projection. -/
theorem exists_relative_section (p : I)
    (sq : IsPushout (d.app p) (e.app p) (i.app p) ((boundary Y).app p))
    [Mono (d.app p)] [Fibration (π.app p)] [WeakEquivalence (π.app p)] :
    ∃ σ : X.obj p ⟶ X'.obj p, d.app p ≫ σ = u.app p ∧ σ ≫ π.app p = 𝟙 _ ∧
      ∃ r : Y.obj p ⟶ (reduced u e).obj p,
        i.app p ≫ r.right = σ ≫ (pushout.inl u e).app p ∧
        r ≫ (projection u e Y π d i hu hi).app p = 𝟙 _ := by
  have hu' : u.app p ≫ π.app p = d.app p := NatTrans.congr_app hu p
  let c : CommSq (u.app p) (d.app p) (π.app p) (𝟙 (X.obj p)) :=
    ⟨hu'.trans (Category.comp_id _).symm⟩
  letI : Cofibration (d.app p) := SSet.modelCategoryQuillen.cofibration_of_mono _
  let σ := c.lift
  have hσ : d.app p ≫ σ = u.app p := c.fac_left
  have hπ : σ ≫ π.app p = 𝟙 _ := c.fac_right
  let l := (pushout.inl u e).app p
  let b := (pushout.inr u e).app p
  have hc : d.app p ≫ (σ ≫ l) = e.app p ≫ b := by
    rw [← Category.assoc, hσ]
    exact NatTrans.congr_app (pushout.condition (f := u) (g := e)) p
  let r : Y.obj p ⟶ (reduced u e).obj p :=
    Under.homMk (sq.desc (σ ≫ l) b hc) (sq.inr_desc _ _ _)
  have hr : i.app p ≫ r.right = σ ≫ l := sq.inl_desc _ _ _
  refine ⟨σ, hσ, hπ, r, hr, ?_⟩
  let ρ := (projection u e Y π d i hu hi).app p
  have hl : l ≫ ρ.right = π.app p ≫ i.app p :=
    descend_cylinder u e Y (π ≫ i) (projection_square u e Y π d i hu hi) p
  change r ≫ ρ = 𝟙 _
  apply Under.UnderMorphism.ext
  apply sq.hom_ext
  · change i.app p ≫ r.right ≫ ρ.right = i.app p ≫ 𝟙 _
    rw [← Category.assoc, hr, Category.assoc, hl, ← Category.assoc, hπ, Category.id_comp,
      Category.comp_id]
  · exact (Under.w (r ≫ ρ)).trans (Under.w (𝟙 (Y.obj p))).symm

/-! A compatible natural lift gives a natural relative section. -/

variable (σ : X ⟶ X') (hσ : d ≫ σ = u)
variable (sq : ∀ p, IsPushout (d.app p) (e.app p) (i.app p) ((boundary Y).app p))
include σ hσ sq

private def naturalRelativeSectionAt (p : I) : Y.obj p ⟶ (reduced u e).obj p := by
  let l := (pushout.inl u e).app p
  let b := (pushout.inr u e).app p
  have hc : d.app p ≫ (σ.app p ≫ l) = e.app p ≫ b := by
    have hσ' : d.app p ≫ σ.app p = u.app p := NatTrans.congr_app hσ p
    rw [← Category.assoc, hσ']
    exact NatTrans.congr_app (pushout.condition (f := u) (g := e)) p
  exact Under.homMk ((sq p).desc (σ.app p ≫ l) b hc) ((sq p).inr_desc _ _ _)

private theorem naturalRelativeSectionAt_cylinder (p : I) :
    i.app p ≫ (naturalRelativeSectionAt u e Y d i σ hσ sq p).right =
      σ.app p ≫ (pushout.inl u e).app p :=
  (sq p).inl_desc _ _ _

/-- A natural relative section induced by a compatible lift of the cylinder. -/
def naturalRelativeSection : Y ⟶ reduced u e where
  app p := naturalRelativeSectionAt u e Y d i σ hσ sq p
  naturality p p' f := by
    apply Under.UnderMorphism.ext
    apply (sq p).hom_ext
    · change i.app p ≫ (Y.map f).right ≫
        (naturalRelativeSectionAt u e Y d i σ hσ sq p').right =
          i.app p ≫ (naturalRelativeSectionAt u e Y d i σ hσ sq p).right ≫
            ((reduced u e).map f).right
      have hi' : i.app p ≫ (Y.map f).right = X.map f ≫ i.app p' :=
        (i.naturality f).symm
      have hσ' : X.map f ≫ σ.app p' = σ.app p ≫ X'.map f :=
        σ.naturality f
      have hl' : X'.map f ≫ (pushout.inl u e).app p' =
          (pushout.inl u e).app p ≫ (pushout u e).map f :=
        (pushout.inl u e).naturality f
      calc
        _ = (i.app p ≫ (Y.map f).right) ≫
            (naturalRelativeSectionAt u e Y d i σ hσ sq p').right :=
              (Category.assoc _ _ _).symm
        _ = (X.map f ≫ i.app p') ≫
            (naturalRelativeSectionAt u e Y d i σ hσ sq p').right :=
              congrArg (· ≫ (naturalRelativeSectionAt u e Y d i σ hσ sq p').right) hi'
        _ = X.map f ≫ (i.app p' ≫
            (naturalRelativeSectionAt u e Y d i σ hσ sq p').right) :=
              Category.assoc _ _ _
        _ = X.map f ≫ (σ.app p' ≫ (pushout.inl u e).app p') :=
              congrArg (X.map f ≫ ·)
                (naturalRelativeSectionAt_cylinder u e Y d i σ hσ sq p')
        _ = (X.map f ≫ σ.app p') ≫ (pushout.inl u e).app p' :=
              (Category.assoc _ _ _).symm
        _ = (σ.app p ≫ X'.map f) ≫ (pushout.inl u e).app p' :=
              congrArg (· ≫ (pushout.inl u e).app p') hσ'
        _ = σ.app p ≫ (X'.map f ≫ (pushout.inl u e).app p') :=
              Category.assoc _ _ _
        _ = σ.app p ≫ ((pushout.inl u e).app p ≫ (pushout u e).map f) :=
              congrArg (σ.app p ≫ ·) hl'
        _ = (σ.app p ≫ (pushout.inl u e).app p) ≫ (pushout u e).map f :=
              (Category.assoc _ _ _).symm
        _ = (i.app p ≫ (naturalRelativeSectionAt u e Y d i σ hσ sq p).right) ≫
            (pushout u e).map f :=
              congrArg (· ≫ (pushout u e).map f)
                (naturalRelativeSectionAt_cylinder u e Y d i σ hσ sq p).symm
        _ = i.app p ≫ (naturalRelativeSectionAt u e Y d i σ hσ sq p).right ≫
            ((reduced u e).map f).right :=
              Category.assoc _ _ _
    · exact (Under.w ((Y.map f) ≫ naturalRelativeSectionAt u e Y d i σ hσ sq p')).trans
        (Under.w (naturalRelativeSectionAt u e Y d i σ hσ sq p ≫
          (reduced u e).map f)).symm

/-- The natural section has the prescribed cylinder component. -/
theorem naturalRelativeSection_cylinder (p : I) :
    i.app p ≫ ((naturalRelativeSection u e Y d i σ hσ sq).app p).right =
      σ.app p ≫ (pushout.inl u e).app p :=
  naturalRelativeSectionAt_cylinder u e Y d i σ hσ sq p

/-- The natural relative section splits the reduced projection exactly. -/
theorem naturalRelativeSection_projection (hπ : σ ≫ π = 𝟙 X) :
    naturalRelativeSection u e Y d i σ hσ sq ≫ projection u e Y π d i hu hi = 𝟙 Y := by
  apply NatTrans.ext
  funext p
  apply Under.UnderMorphism.ext
  apply (sq p).hom_ext
  · change i.app p ≫
      ((naturalRelativeSection u e Y d i σ hσ sq).app p).right ≫
      ((projection u e Y π d i hu hi).app p).right = i.app p ≫ 𝟙 _
    have hπ' : σ.app p ≫ π.app p = 𝟙 _ := NatTrans.congr_app hπ p
    have hl : (pushout.inl u e).app p ≫
        ((projection u e Y π d i hu hi).app p).right = π.app p ≫ i.app p :=
      descend_cylinder u e Y (π ≫ i) (projection_square u e Y π d i hu hi) p
    rw [← Category.assoc, naturalRelativeSection_cylinder u e Y d i σ hσ sq p,
      Category.assoc, hl,
      ← Category.assoc, hπ', Category.id_comp, Category.comp_id]
  · exact (Under.w (((naturalRelativeSection u e Y d i σ hσ sq).app p) ≫
      ((projection u e Y π d i hu hi).app p))).trans
      (Under.w (𝟙 (Y.obj p))).symm

end

end DaggerModels.PartII.JTEndpointReducedCover
