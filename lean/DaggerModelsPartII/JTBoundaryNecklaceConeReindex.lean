import DaggerModelsPartII.JTBoundaryNecklacePresentationCone
import DaggerModelsPartII.JTCylinderOverTargetBaseChangeTime

/-!
# Restriction of the boundary necklace cone along a map under the boundary
-/

set_option autoImplicit false

open CategoryTheory Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTBoundaryNecklaceConeReindex

open BoundaryNecklaceComma (necklaceUnder sourceCode)
open JTBoundaryNecklacePresentationCone (cone cone_base cone_native_map)
open JTCylinderOverTargetBaseChangeTime (source_eq)

noncomputable section

private abbrev B := JTXiEndpointCollapse.boundary

/-- The cone components are unchanged by restricting the cylinder and collapse
along the same boundary-preserving map. -/
theorem cone_reindex {I : Type} [SmallCategory I] (E : I ⥤ Under B)
    {i : I} {A₀ A : Under B} (U : BoundaryNecklaceComma.Presentation E)
    (p₀ : A₀ ⟶ E.obj i) (p : A ⟶ E.obj i) (a₀ a : i ⟶ U.base)
    (b₀ : A₀ ⟶ necklaceUnder.obj U.fiber.left)
    (b : A ⟶ necklaceUnder.obj U.fiber.left) (u : A₀ ⟶ A)
    (hp : u ≫ p = p₀) (hb : u ≫ b = b₀) (ha : a = a₀)
    (h₀ : p₀ ≫ E.map a₀ = b₀ ≫ U.fiber.hom)
    (h : p ≫ E.map a = b ≫ U.fiber.hom) :
    Functor.whiskerLeft (CostructuredArrow.map u) (cone E p U a b h) =
      eqToHom (source_eq E p₀ p u hp) ≫ cone E p₀ U a₀ b₀ h₀ := by
  subst a₀
  ext : 1
  funext P
  apply JTTargetCommaPullback.operator_ext
  · simp only [Functor.whiskerLeft_app, NatTrans.comp_app, cone_base,
      eqToHom_app, Grothendieck.comp_base, Grothendieck.base_eqToHom]
    exact (Category.id_comp a).symm
  · let C := sourceCode E
    change C.map ((Functor.whiskerLeft (CostructuredArrow.map u) (cone E p U a b h)).app P) =
      C.map ((eqToHom (source_eq E p₀ p u hp) ≫ cone E p₀ U a b₀ h₀).app P)
    simp only [Functor.whiskerLeft_app, NatTrans.comp_app, eqToHom_app, Functor.map_comp,
      eqToHom_map]
    change C.map ((cone E p U a b h).app ((CostructuredArrow.map u).obj P)) =
      𝟙 P.left ≫ C.map ((cone E p₀ U a b₀ h₀).app P)
    rw [Category.id_comp]
    apply NecklaceCode.Hom.ext
    change ((cone E p U a b h).app ((CostructuredArrow.map u).obj P)).fiber.left.map =
      ((cone E p₀ U a b₀ h₀).app P).fiber.left.map
    rw [cone_native_map, cone_native_map]
    change ((P.hom ≫ u) ≫ b).right = (P.hom ≫ b₀).right
    rw [Category.assoc, hb]

section Slice

variable {J J₀ C D : Type*} [Category* J] [Category* J₀] [Category* C] [Category* D]

/-- Map a cone and then compose its legs with a fixed arrow. -/
def mapCone {F : J ⥤ C} {X : C} (τ : F ⟶ (Functor.const J).obj X)
    (K : C ⥤ D) {Y : D} (k : K.obj X ⟶ Y) :
    F ⋙ K ⟶ (Functor.const J).obj Y :=
  Functor.whiskerRight τ K ≫ (Functor.constComp J X K).hom ≫ (Functor.const J).map k

/-- Mapping the cones preserves their restriction equality. -/
theorem mapCone_reindex (M : J₀ ⥤ J) {F : J ⥤ C} {F₀ : J₀ ⥤ C}
    {X : C} (τ : F ⟶ (Functor.const J).obj X) (τ₀ : F₀ ⟶ (Functor.const J₀).obj X)
    (hF : M ⋙ F = F₀)
    (hτ : Functor.whiskerLeft M τ = eqToHom hF ≫ τ₀)
    (K : C ⥤ D) {Y : D} (k : K.obj X ⟶ Y) :
    Functor.whiskerLeft M (mapCone τ K k) =
      eqToHom (congrArg (fun G ↦ G ⋙ K) hF) ≫ mapCone τ₀ K k := by
  subst F₀
  simp only [eqToHom_refl, Category.id_comp] at hτ ⊢
  subst τ₀
  rfl

/-- A compatible restriction of cones gives equality of their slice functors. -/
theorem overLift_reindex (M : J₀ ⥤ J) {F : J ⥤ C} {F₀ : J₀ ⥤ C}
    {X : C} (τ : F ⟶ (Functor.const J).obj X) (τ₀ : F₀ ⟶ (Functor.const J₀).obj X)
    (hF : M ⋙ F = F₀)
    (hτ : Functor.whiskerLeft M τ = eqToHom hF ≫ τ₀) :
    M ⋙ Over.lift F τ = Over.lift F₀ τ₀ := by
  subst F₀
  simp only [eqToHom_refl, Category.id_comp] at hτ
  subst τ₀
  rfl

end Slice

end

end DaggerModels.PartII.JTBoundaryNecklaceConeReindex
